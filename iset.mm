$( iset.mm - Version of 21-Jul-2015

Created by Mario Carneiro, starting from the 21-Jan-2015 version of
set.mm

#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
         Metamath source file for intuitionistic logic and set theory
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/

Maintainer and default contributor:

NM  Norman Megill - http://us.metamath.org/email.html

Contributor list:

DA  David Abernethy      DH  David Harvey           MO  Mel L. O'Cat
SA  Stefan Allan         JH  Jeff Hoffman           SO  Stefan O'Rear
JA  Juha Arpiainen       SJ  Szymon Jaroszewicz     JO  Jason Orendorff
JBN Jonathan Ben-Naim    WL  Wolf Lammen            JP  Josh Purinton
GB  Gregory Bush         GL  Gerard Lang            SR  Steve Rodriguez
MC  Mario Carneiro       RL  Raph Levien            ATS Andrew Salmon
PC  Paul Chapman         FL  Frederic Line          AS  Alan Sare
SF  Scott Fenton         RFL Roy F. Longton         ES  Eric Schmidt
JGH Jeffrey Hankins      JM  Jeff Madsen            DAW David A. Wheeler
AH  Anthony Hart         RM  Rodolfo Medina

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          Contents of this header
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

1. Recent label changes
2. Quick "How To"
3. Bibliography
4. Metamath syntax summary
5. Other notes
6. Acceptable shorter proofs

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          1. Recent label changes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

This is part of an ongoing project to improve naming consistency.  If you have
suggestions for better names, let me know.

To update your mathbox, you can make can make global substitutions into
your local version by processing the ones WITHOUT "Notes" in _reverse_ order.
The ones WITH "Notes" may have to be processed manually.

PROPOSED:
Date      Old       New         Notes
proposed  syl       imtri       (analogous to *bitr*, sstri, etc.)
proposed  sylib     imbitri     etc.
proposed  sylbid    biimtrd     etc.
proposed  sylbird   biimtrrd    etc.
proposed  syl5*     *trid       (syl5bi -> biimtrid; syl5eqel -> eqeltrid;etc.)
proposed  syl6*     *trdi
proposed  *mpt*     *mpf* or *mptf* (maps-to for functions)
proposed  *mpt2*    *mpo* or *mpto* (maps-to for operations)
(Please send any comments on these proposals to Norm Megill.)

DONE:
Date      Old       New         Notes
28-Jan-15 strssd    [--same--]  moved from NM's mathbox to main set.mm
28-Jan-15 strfvd    [--same--]  moved from NM's mathbox to main set.mm
28-Jan-15 strfvnd   [--same--]  moved from NM's mathbox to main set.mm
28-Jan-15 r1omNEW   r1om        moved from SO's mathbox to main set.mm
28-Jan-15 ackbij2   [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 ackbij1b  [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 ackbij1   [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 onpsssuc  [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 f1opw     [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 djudisj   [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 djussxp   [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 xpsnen2g  [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 nnunifi   [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 fzsdom2   [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 hashfz    [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 isinffi   [--same--]  moved from SO's mathbox to main set.mm
28-Jan-15 isprj2    [--same--]  (in FL's mathbox) revised
28-Jan-15 prdmbasex [--same--]  revised
28-Jan-15 ixpexg    [--same--]  revised
19-Jan-15 ---       ---         strlemor0 ~ prdmlmodd moved from SO's mathbox
                                to main set.mm
19-Jan-15 lspf      [--same--]  moved from SO's mathbox to main set.mm
19-Jan-15 lsslsp    [--same--]  moved from SO's mathbox to main set.mm
19-Jan-15 lsslss    [--same--]  moved from SO's mathbox to main set.mm
19-Jan-15 ---       ---         cghm ~ reslmhm moved from SO's mathbox to main
                                set.mm
19-Jan-15 elfz1end  [--same--]  moved from SO's mathbox to main set.mm
19-Jan-15 curgrpact [--same--]  (in FL's mathbox) revised
19-Jan-15 rngapm    [--same--]  (in FL's mathbox) revised
19-Jan-15 gapm2     [--same--]  (in FL's mathbox) revised
19-Jan-15 gaplc     galcan      moved from FL's mathbox to main set.mm; revised
19-Jan-15 symgfo    [--same--]  (in FL's mathbox) revised
19-Jan-15 ltlga     gaid2       moved from FL's mathbox to main set.mm; revised
19-Jan-15 cayleyth  [--same--]  moved from PC's mathbox to main set.mm; revised
19-Jan-15 cayleyi   cayley      moved from PC's mathbox to main set.mm; revised
19-Jan-15 symggrp   [--same--]  moved from PC's mathbox to main set.mm; revised
19-Jan-15 tgss      [--same--]  revised
19-Jan-15 unitg     [--same--]  revised
19-Jan-15 bastg     [--same--]  revised
19-Jan-15 tg2       [--same--]  revised
19-Jan-15 tg1       [--same--]  revised
19-Jan-15 eltg2b    [--same--]  revised
19-Jan-15 eltg2     [--same--]  revised
19-Jan-15 eltg      [--same--]  revised
19-Jan-15 tgval2    [--same--]  revised
19-Jan-15 tgval     [--same--]  revised
19-Jan-15 df-topgen [--same--]  revised
19-Jan-15 symgidi   symgid      revised
19-Jan-15 symggrpi  symggrp     revised
19-Jan-15 symgov    [--same--]  revised
19-Jan-15 symgval   symgplusg   revised
19-Jan-15 elsymgrn  elsymgbas   revised
19-Jan-15 df-symg   [--same--]  revised
19-Jan-15 gapm      [--same--]  revised
19-Jan-15 gacan     [--same--]  revised
19-Jan-15 gaass     [--same--]  revised
19-Jan-15 gagrpid   [--same--]  revised
19-Jan-15 gaf       [--same--]  revised
19-Jan-15 gagrp     [--same--]  revised
19-Jan-15 ssga      subgga      revised
19-Jan-15 gaid      [--same--]  revised
19-Jan-15 ga0       [--same--]  revised
19-Jan-15 isga2     ---         deleted; use isga
19-Jan-15 gafo      [--same--]  revised
19-Jan-15 isga      [--same--]  revised
19-Jan-15 df-ga     [--same--]  revised
19-Jan-15 grplactf1o [--same--] revised
19-Jan-15 grplactval [--same--] revised
19-Jan-15 grplactfval [--same--] revised
19-Jan-15 islbs2    islbs3      revised
19-Jan-15 lbspss    [--same--]  revised
19-Jan-15 lbsind    lbsind2     revised
19-Jan-15 lbssp     [--same--]  revised
19-Jan-15 lbsel     [--same--]  revised
19-Jan-15 lbsss     [--same--]  revised
19-Jan-15 islbs     [--same--]  revised; see also islbs2
19-Jan-15 lbsval    ---         deleted; use islbs
19-Jan-15 df-lbs    [--same--]  revised
19-Jan-15 lssne0    [--same--]  revised
19-Jan-15 lsscl     [--same--]  revised
19-Jan-15 lssn0     [--same--]  revised
19-Jan-15 lssel     [--same--]  revised
19-Jan-15 lssss     [--same--]  revised
19-Jan-15 islssd    [--same--]  revised
19-Jan-15 islss     [--same--]  revised
19-Jan-15 lagsubglem2 lagsubg2  revised
19-Jan-15 lagsubglem1 eqger     revised
19-Jan-15 issubg2   [--same--]  revised
19-Jan-15 odphi     odzphi
19-Jan-15 oddvds    odzdvds
19-Jan-15 odid      odzid
19-Jan-15 odcl      odzcl
19-Jan-15 odcllem   odzcllem
19-Jan-15 odval     odzval
19-Jan-15 df-od     df-odz
19-Jan-15 cod       codz
19-Jan-15 ---       ---         math token "od" changed to "odZ"
10-Jan-15 lsmss1xxx lsmss2
10-Jan-15 lsmss1    lsmss2
10-Jan-15 lsmss2    lsmss1xxx
 9-Jan-15 mpbiran   [--same--]  changed hypothesis order
 9-Jan-15 mpbiran2  [--same--]  changed hypothesis order
 9-Jan-15 mpbir2an  [--same--]  changed hypothesis order
 9-Jan-15 mpbi2and  [--same--]  changed hypothesis order
 9-Jan-15 mpbir2and [--same--]  changed hypothesis order
 9-Jan-15 mpbir3an  [--same--]  changed hypothesis order
 9-Jan-15 mpbir3and [--same--]  changed hypothesis order
 8-Jan-15 lsmmod    [--same--]  swapped equality arguments
 8-Jan-15 ficarddom [--same--]  swapped biconditional arguments
 7-Jan-15 algvsca   [--same--]  moved from SO's mathbox to main set.mm
 7-Jan-15 algsca    [--same--]  moved from SO's mathbox to main set.mm
 7-Jan-15 algmulr   [--same--]  moved from SO's mathbox to main set.mm
 7-Jan-15 algaddg   [--same--]  moved from SO's mathbox to main set.mm
 7-Jan-15 algbase   [--same--]  moved from SO's mathbox to main set.mm
 7-Jan-15 algfun    [--same--]  moved from SO's mathbox to main set.mm
 7-Jan-15 algfn     [--same--]  moved from SO's mathbox to main set.mm
 7-Jan-15 crngcom   crngocom
 7-Jan-15 ---       ---         math token "CRing" changed to "CRingOps"
 7-Jan-15 df-mnd2   df-mnd      moved from FL's mathbox to main set.mm
 7-Jan-15 mndass2   mndoass2
 7-Jan-15 mndass    mndoass
 7-Jan-15 mndio     mndoio
 7-Jan-15 mndid     mndoid
 7-Jan-15 mndisass  mndoisass
 7-Jan-15 df-tsms   rngomndo
 7-Jan-15 rngomnd   rngomndo
 7-Jan-15 grpomnd   grpomndo
 7-Jan-15 ismnd2    ismndo2
 7-Jan-15 ismnd1    ismndo1
 7-Jan-15 ismnd     ismndo
 7-Jan-15 mndmgmid  mndomgmid
 7-Jan-15 mndismgm  mndoismgm
 7-Jan-15 mndisexid mndoisexid
 7-Jan-15 mndissmgrp mndoissmgrp
 7-Jan-15 df-mnd    df-mndo
 7-Jan-15 cmnd      cmndo
 7-Jan-15 ---       ---         math token "Mnd" changed to "MndOp"
 7-Jan-15 grp2grpo  ---         deleted (commented out)
 7-Jan-15 unitpropd [--same--]  revised: eliminated hypothesis
 7-Jan-15 dvdsrpropd [--same--] revised: eliminated hypothesis
 7-Jan-15 dvdsrmul2 dvdsrmul1   revised
 7-Jan-15 dvdsrmul  [--same--]  revised
 7-Jan-15 dvdsr2    [--same--]  revised
 7-Jan-15 dvdsr     [--same--]  revised
 7-Jan-15 dvdsrval  [--same--]  revised
 7-Jan-15 df-dvdsr  [--same--]  revised (changed from left-divisible to right)
 7-Jan-15 ringi     [--same--]  revised
 7-Jan-15 isring    [--same--]  revised
 7-Jan-15 df-ring   [--same--]  revised
 7-Jan-15 gsum2d    [--same--]  revised
 7-Jan-15 ---       ---         all gsum* theorems revised for CMnd
 7-Jan-15 mulgnndi  mulgnn0di   revised
 7-Jan-15 abl4      cmn4        revised
 7-Jan-15 abl32     cmn32       revised
 7-Jan-15 isabld    [--same--]  reordered hypotheses
 7-Jan-15 isabl     isabl2
 7-Jan-15 df-abl    [--same--]  revised
 7-Jan-15 mulgnn0ass [--same--] revised
 7-Jan-15 mulgnnass [--same--]  revised
 7-Jan-15 mulgnn0dir [--same--] revised
 7-Jan-15 mulgnndir [--same--]  revised
 7-Jan-15 mulgnn0z  [--same--]  revised
 7-Jan-15 mulgnn0cl [--same--]  revised
 7-Jan-15 mulgnncl  [--same--]  revised
 7-Jan-15 mulgnn0p1 [--same--]  revised
 7-Jan-15 grpinv    ---         deleted; use grplinv, grprinv
 7-Jan-15 isgrpid   ---         deleted; use ismgmid
 7-Jan-15 grpidinv2 ---         deleted; use grplid, grprid, grpinvex
 7-Jan-15 isgrpi    [--same--]  revised: eliminated hypothesis
 7-Jan-15 isgrpiOLD ---         deleted
 7-Jan-15 isgrpdOLD ---         deleted
 7-Jan-15 isgrprd   ---         deleted
 7-Jan-15 isgrpd    [--same--]  revised: eliminated hypothesis
 7-Jan-15 grppropOLD ---        deleted; use grpprop
 7-Jan-15 elgrp     ---         deleted; use isgrp
 7-Jan-15 grpideu2  ---         deleted; use grpideu or grpridd
 7-Jan-15 grpidinv  ---         deleted; use grpinvex
 7-Jan-15 ---       ---         grpidinvlem1 - grpidinvlem4 deleted
 7-Jan-15 grplidinv             deleted; use grpinvex
 7-Jan-15 grplem1   ---         deleted
 7-Jan-15 isgrp2    ---         deleted; use isgrp
 7-Jan-15 isgrp     [--same--]  revised
 7-Jan-15 df-grp    [--same--]  revised
 7-Jan-15 df-mpq    [--same--]  revised
 7-Jan-15 df-plpq   [--same--]  revised
 7-Jan-15 fineqv    [--same--]  revised
 7-Jan-15 erovlem   [--same--]  revised
 7-Jan-15 eroveu    [--same--]  revised
 7-Jan-15 ovmpt2    [--same--]  changed distinct vars
 7-Jan-15 ovmpt2g   [--same--]  changed distinct vars
 7-Jan-15 grplidd   grpridd     revised
 7-Jan-15 grplinvd  grprinvd    revised
 7-Jan-15 grplinvlem2 ---       deleted
 7-Jan-15 grplinvlem1 grprinvlem revised
 7-Jan-15 caovcld   caovclg
 7-Jan-15 posn      [--same--]  revised
 7-Jan-15 sbcbidv   sbcbidgv
 7-Jan-15 sbcbid    sbcbidg
28-Dec-14 grpnegprop ---        (in SO's mathbox) deleted; use grpinvpropd
28-Dec-14 grpidprop ---         (in SO's mathbox) deleted; use grpidpropd
28-Dec-14 fvco4     fvco2       moved from SO's mathbox to main set.mm
28-Dec-14 injrec    [--same--]  (in FL's mathbox) revised
28-Dec-14 subrgugrp [--same--]  revised
28-Dec-14 drngid    [--same--]  revised
28-Dec-14 drngmgrp  [--same--]  revised
28-Dec-14 isdrng2   [--same--]  revised
28-Dec-14 invrfval  [--same--]  revised
28-Dec-14 df-invr   [--same--]  revised
28-Dec-14 unitgrpid [--same--]  revised
28-Dec-14 unitgrp   [--same--]  revised
28-Dec-14 rngidval  [--same--]  revised
28-Dec-14 df-ur     [--same--]  revised
28-Dec-14 df-gsum   [--same--]  revised
28-Dec-14 grpsubval [--same--]  revised: eliminated hypothesis
28-Dec-14 grpidval  [--same--]  revised
28-Dec-14 grpproplem proplem
28-Dec-14 grpproplem2 proplem2
28-Dec-14 grpideu   grpideu2
28-Dec-14 df-0g     [--same--]  revised
28-Dec-14 algrflem  [--same--]  revised: eliminated hypothesis
28-Dec-14 fvco3     [--same--]  revised: eliminated hypothesis
28-Dec-14 fvco2     [--same--]  revised: eliminated hypothesis
28-Dec-14 fvco      [--same--]  revised: eliminated hypothesis
28-Dec-14 hbcsb1    [--same--]  revised: eliminated hypothesis
28-Dec-14 hbsbc1    hbsbc1g2
27-Dec-14 a1i12     a1ii
27-Dec-14 fmpt2d    [--same--]  revised: weakened hypothesis
 5-Dec-14 df-cnfld  [--same--]  moved from SO's mathbox to main set.mm
 5-Dec-14 grppropd  [--same--]  moved from SO's mathbox to main set.mm
 5-Dec-14 df-ress   [--same--]  moved from SO's mathbox to main set.mm
 5-Dec-14 ghsubg    ghsubgo
 5-Dec-14 zaddsubg  zaddsubgo
 5-Dec-14 readdsubg readdsubgo
 5-Dec-14 subgablo  subgoablo
 5-Dec-14 issubgi   issubgoi
 5-Dec-14 subginv   subgoinv
 5-Dec-14 subgid    subgoid
 5-Dec-14 subgrnss  subgornss
 5-Dec-14 subgov    subgoov
 5-Dec-14 subgres   subgores
 5-Dec-14 issubg    issubgo
 5-Dec-14 df-subg   df-subgo
 5-Dec-14 csubg     csubgo
 5-Dec-14 isabvd    [--same--]  revised
 5-Dec-14 rngdvcan1 [--same--]  revised
 5-Dec-14 rngdvcl   [--same--]  revised
 5-Dec-14 rngdvval  [--same--]  revised
 5-Dec-14 rngdvfval [--same--]  revised
 5-Dec-14 rngnegrmul rngmneg2   revised
 5-Dec-14 rngneglmul rngmneg1   revised
 5-Dec-14 isrngd    [--same--]  revised
 5-Dec-14 isrng     [--same--]  revised
 5-Dec-14 df-ring   [--same--]  revised
 5-Dec-14 lagsubg   [--same--]  revised
 5-Dec-14 grpn0     grpbn0
 5-Dec-14 setsval   [--same--]  revised
 5-Dec-14 df-sets   [--same--]  revised
10-Nov-14 dford3    dford5reg   (in SF's mathbox)
10-Nov-14 fvun2     [--same--]  moved from SF's mathbox to main set.mm
10-Nov-14 fvun1     [--same--]  moved from SF's mathbox to main set.mm
10-Nov-14 twsvbdop  oprab4      moved from FL's mathbox to main set.mm
10-Nov-14 ra42e     [--same--]  moved from FL's mathbox to main set.mm
10-Nov-14 dmmptss   [--same--]  moved from SF's mathbox to main set.mm
10-Nov-14 rabxm     [--same--]  moved from JM's mathbox to main set.mm
10-Nov-14 rabnc     [--same--]  moved from JM's mathbox to main set.mm
10-Nov-14 absz      [--same--]  moved from JM's mathbox to main set.mm
10-Nov-14 absmod0   [--same--]  moved from JM's mathbox to main set.mm
10-Nov-14 negmod0   [--same--]  moved from JM's mathbox to main set.mm
13-Oct-14 qredeu    [--same--]  moved from JGH's mathbox to main set.mm
13-Oct-14 qredeq    [--same--]  moved from JGH's mathbox to main set.mm
25-Sep-14 otthg     otthg2      otthg now uses ordered triple definition
23-Sep-14 logcl     logrncl
23-Sep-14 divcnlem  reccn2      revised
23-Sep-14 climsqueeze2 climsqz2
23-Sep-14 climsqueeze climsqz
21-Sep-14 elqs2     ---         (in RM's mathbox) deleted; same as elqsg
21-Sep-14 cnss      ---         (in JM's mathbox) deleted; same as cnsubsp2r
21-Sep-14 elnnr     ---         (in JM's mathbox) deleted; same as elrege0
21-Sep-14 zmodfzcl  ---         (in JM's mathbox) deleted; same as zmodfz
21-Sep-14 subtareqbe [--same--] (in FL's mathbox) revised
21-Sep-14 subtsm    [--same--]  (in FL's mathbox) revised
21-Sep-14 pwtsm     [--same--]  (in FL's mathbox) revised
21-Sep-14 tmpts     tskmcl      moved from FL's mathbox to main set.mm; revised
21-Sep-14 intrtael  tskint      moved from FL's mathbox to main set.mm; revised
21-Sep-14 intartar  inttsk      moved from FL's mathbox to main set.mm
21-Sep-14 inttar1   ---         (in FL's mathbox) deleted; see 0tsk
21-Sep-14 elttar    tskmid      moved from FL's mathbox to main set.mm
21-Sep-14 btmp      eltskm      moved from FL's mathbox to main set.mm; revised
21-Sep-14 bpmp      sstskm      moved from FL's mathbox to main set.mm; revised
21-Sep-14 tarval2g  tskmval     moved from FL's mathbox to main set.mm; revised
21-Sep-14 tarval2   ---         (in FL's mathbox) deleted; see tskmval
21-Sep-14 df-tskmp  df-tskm     moved from FL's mathbox to main set.mm; revised
21-Sep-14 ctarskim  ctskm
21-Sep-14 tarsuc3   ---         (in FL's mathbox) deleted; see tsktrss
21-Sep-14 tarsuc2   tsksuc      moved from FL's mathbox to main set.mm; revised
21-Sep-14 tarsuc1   ---         (in FL's mathbox) deleted; see tsksuc, tsktrss
21-Sep-14 sexptrt   tskmap      moved from FL's mathbox to main set.mm; revised
21-Sep-14 cptarc    tskxp       moved from FL's mathbox to main set.mm; revised
21-Sep-14 tclinf    ---         (in FL's mathbox) deleted; same as tskinf
21-Sep-14 tartord   ---         (in FL's mathbox) deleted; see tsktrss
21-Sep-14 tartrel   tsktrss     moved from FL's mathbox to main set.mm
21-Sep-14 elcartr   ---         (in FL's mathbox) deleted; see trss
21-Sep-14 tarax3d4  ---         (in FL's mathbox) deleted; see tsksdom
21-Sep-14 tarax3d3  ---         (in FL's mathbox) deleted; see tsksdom
21-Sep-14 tarax3c   ---         (in FL's mathbox) deleted; see tsken
21-Sep-14 tarax3b   ---         (in FL's mathbox) deleted; see tsken
21-Sep-14 tarax3a   ---         (in FL's mathbox) deleted; same as tsken
21-Sep-14 inacint   tskin       moved from FL's mathbox to main set.mm; revised
21-Sep-14 elincin   ---         (in FL's mathbox) deleted; same as tskss
21-Sep-14 letri31   ---         (in FL's mathbox) deleted; same as xrletri3
21-Sep-14 elioooord ---         (in FL's mathbox) deleted; same as eliooord
21-Sep-14 elioc3    ---         (in FL's mathbox) deleted; same as elioc2
21-Sep-14 elico3    ---         (in FL's mathbox) deleted; same as elico2
21-Sep-14 omslim2   ---         (in FL's mathbox) deleted; same as dfom5
21-Sep-14 omslim    ---         (in FL's mathbox) deleted; see dfom5
21-Sep-14 ltwefz    [--same--]  moved from SF's mathbox to main set.mm
21-Sep-14 ltwenn    [--same--]  moved from SF's mathbox to main set.mm
21-Sep-14 ltweuz    [--same--]  moved from SF's mathbox to main set.mm
21-Sep-14 sqrrpcl   ---         deleted; same as rpsqrcl
21-Sep-14 ltfrn     ltweuz
21-Sep-14 zmodcl2   zmodfz
21-Sep-14 tskssel2  ---         deleted; see tskssel
21-Sep-14 eltsk2    ---         deleted; see eltsk2g
21-Sep-14 eltsk     ---         deleted; see eltskg
21-Sep-14 dftsk2    ---         deleted; see eltsk2g
21-Sep-14 omsubinit alephinit
21-Sep-14 infenomsub infenaleph
21-Sep-14 omsubindss ---        deleted; same as alephle
21-Sep-14 omsublim  ---         deleted; see alephislim
21-Sep-14 omsubdmss alephdom2
21-Sep-14 elomsubsd alephsdom
21-Sep-14 omsubss   ---         deleted; same as alephord3
21-Sep-14 omsubel   ---         deleted; same as alephord2
21-Sep-14 omsubdom  alephdom
21-Sep-14 omsubsdom ---         deleted; same as alephordi
21-Sep-14 omsubsdomlem2 ---     deleted; see alephordi
21-Sep-14 omsubsdomlem1 ---     deleted; same as alephordilem1
21-Sep-14 omsubsuc2 ---         deleted; same as alephsuc2
21-Sep-14 omsubsuc  ---         deleted; same as alephsuc
19-Sep-14 clfsebs2  ---         (in FL's mathbox) deleted; same as clfsebsr
15-Sep-14 ostth     [--same--]  revised
15-Sep-14 wlogle    [--same--]  revised
11-Sep-14 infmrgelbOLD ---      (in JM's mathbox) deleted; see infmrgelb
11-Sep-14 lbleinfOLD ---        (in JGH's mathbox) deleted; see infmrgelb
11-Sep-14 suplub2   supwlub     (in FL's mathbox)
11-Sep-14 nmfnleub  [--same--]  revised
11-Sep-14 nmopub    [--same--]  revised
11-Sep-14 itg2leub  [--same--]  revised
11-Sep-14 mbfmono   mbfsup      revised
11-Sep-14 ovolshftlem2 [--same--] revised
11-Sep-14 nmoubi    [--same--]  revised
11-Sep-14 pcid      pcidlem
11-Sep-14 caurcvg   [--same--]  revised
11-Sep-14 caurcvglem [--same--] revised
11-Sep-14 limsupcl  [--same--]  revised
11-Sep-14 limsupval [--same--]  revised
11-Sep-14 expcl2lem [--same--]  revised
11-Sep-14 infmxrgelb [--same--] revised
11-Sep-14 infmrgelb [--same--]  revised
11-Sep-14 suprleubii [--same--] revised
11-Sep-14 suprnubii [--same--]  revised
11-Sep-14 suprlubii [--same--]  revised
11-Sep-14 suprleub  [--same--]  revised
11-Sep-14 suprnub   [--same--]  revised
11-Sep-14 suprlub   [--same--]  revised
 2-Sep-14 grpohlem5 grpohmlem5  (in FL's mathbox)
 2-Sep-14 grpohlem3 grpohmlem3  (in FL's mathbox)
 2-Sep-14 ditgsplit [--same--]  revised
 2-Sep-14 ditgswap  [--same--]  revised
 2-Sep-14 ditgcl    [--same--]  revised
 2-Sep-14 ditgneg   [--same--]  revised
 2-Sep-14 ditgpos   [--same--]  revised
 2-Sep-14 mbfeq     mbfeqa      revised
 2-Sep-14 ivthicc   [--same--]  revised
 2-Sep-14 ivthle2   [--same--]  revised
 2-Sep-14 ivthle    [--same--]  revised
 2-Sep-14 ivth2     [--same--]  revised
 2-Sep-14 ivth      [--same--]  revised
 2-Sep-14 negfcncf  [--same--]  revised
 2-Sep-14 cncfco    [--same--]  revised
 2-Sep-14 cncffvrn  [--same--]  revised
 2-Sep-14 rescncf   [--same--]  revised
 2-Sep-14 cncffvelrn ---        deleted; see cncff
 2-Sep-14 cncfi     [--same--]  revised
 2-Sep-14 cncffvelrnOLD ---     deleted; see cncff
 2-Sep-14 cncff     [--same--]  revised
 2-Sep-14 ---       ---         changed math symbol from "Itgbl" to "L^1"
18-Aug-14 reheibor  [--same--]  (in JM's mathbox) revised
18-Aug-14 itgcnval  [--same--]  revised
18-Aug-14 iblre     iblrelem
18-Aug-14 itg0      itgz
18-Aug-14 mbfneg    [--same--]  revised
18-Aug-14 mbfmulc2  mbfmulc2re  revised
18-Aug-14 iccst     ---         deleted; see resubmet
18-Aug-14 stioo     ---         deleted; see resubmet
14-Aug-14 rexxfr    [--same--]  revised to be more general
14-Aug-14 ralxfr    [--same--]  revised to be more general
14-Aug-14 rexxfrd   [--same--]  revised to be more general
14-Aug-14 ralxfrd   [--same--]  revised to be more general
10-Aug-14 subntr    [--same--]  moved from JGH's mathbox to main set.mm
10-Aug-14 subcls    [--same--]  moved from JGH's mathbox to main set.mm
10-Aug-14 subsubtop [--same--]  moved from JGH's mathbox to main set.mm
10-Aug-14 ntrin     [--same--]  moved from JGH's mathbox to main set.mm
10-Aug-14 epr       [--same--]  moved from JGH's mathbox to main set.mm
10-Aug-14 epos      [--same--]  moved from JGH's mathbox to main set.mm
10-Aug-14 imrescl   resima2     moved from FL's mathbox to main set.mm
10-Aug-14 dmdcan    [--same--]  moved from SF's mathbox to main set.mm
10-Aug-14 bposlem6  [--same--]  revised
10-Aug-14 bposlem5  [--same--]  revised
10-Aug-14 hashpwlem ---         deleted
30-Jul-14 hasheq0   [--same--]  revised
30-Jul-14 ifswap    ifnot
30-Jul-14 ifor      ifeqor
23-Jul-14 reptertr4 ---         (in FL's mathbox) deleted; see fmptco
23-Jul-14 reptertr3 ---         (in FL's mathbox) deleted; see fmptco
23-Jul-14 reptertr2 ---         (in FL's mathbox) deleted; see fmptco
23-Jul-14 eflti     ---         deleted; see eflt
23-Jul-14 fsumcllem [--same--]  revised
23-Jul-14 fsumcl2lem [--same--] revised
16-Jul-14 cbvrex2v  [--same--]  moved from FL's mathbox to main set.mm
16-Jul-14 df-subg   [--same--]  revised
16-Jul-14 imcj      imval2
16-Jul-14 recj      reval
16-Jul-14 hashf     [--same--]  revised
16-Jul-14 df-hash   [--same--]  revised
16-Jul-14 crmuli    ---         deleted (contents moved to remullem)
14-Jul-14 riota4    riotasbc
14-Jul-14 reiota4   reiotasbc
14-Jul-14 reuuni4   reuunisbc
14-Jul-14 elabs     elabsbc
12-Jul-14 lssdisj   lssdisj1
11-Jul-14 0nelqs2   elqsn0      moved from RM's mathbox to main set.mm; revised
11-Jul-14 erdisj3   qsdisj      moved from RM's mathbox to main set.mm; revised
11-Jul-14 df-subg   [--same--]  revised
11-Jul-14 subgov    [--same--]  revised
11-Jul-14 df-subg   [--same--]  revised
11-Jul-14 hash0     hasheq0
11-Jul-14 dmmulnq   mulnqf      revised
11-Jul-14 dmaddnq   addnqf      revised
11-Jul-14 df-rq     [--same--]  revised
11-Jul-14 ecelqsdm  [--same--]  revised
11-Jul-14 0nelqs    elqsn0      revised
11-Jul-14 uniqs     [--same--]  revised
11-Jul-14 qsexg     [--same--]  revised
11-Jul-14 ecelqsg   [--same--]  changed variable names
11-Jul-14 ecdmn0    [--same--]  revised
11-Jul-14 erdisj2   erdisj      revised
11-Jul-14 erdisj    [--same--]  revised
11-Jul-14 ereldm    ereldmb     revised
11-Jul-14 erthdmr   erth2       revised
11-Jul-14 erthdmg   erth        revised
11-Jul-14 erthdm    erth        revised
11-Jul-14 erth      [--same--]  revised
11-Jul-14 erthi     [--same--]  revised
11-Jul-14 ecdmn0    [--same--]  revised
11-Jul-14 eceq2     eceq1       (these labels should be
11-Jul-14 eceq1     eceq2        exchanged at the same time)
11-Jul-14 erdmrn    [--same--]  revised
11-Jul-14 erref     [--same--]  revised
11-Jul-14 errtr     [--same--]  revised
11-Jul-14 erref2    erref       revised
11-Jul-14 ertr      [--same--]  revised
11-Jul-14 errsym    [--same--]  revised
11-Jul-14 ersymb    [--same--]  revised
11-Jul-14 ersym     [--same--]  revised
11-Jul-14 ster      iser
11-Jul-14 dfec2     [--same--]  revised
11-Jul-14 so        isso2i      revised
11-Jul-14 itlso     issoi
 7-Jul-14 difxpOLD  ---         deleted; see difxp
 7-Jul-14 clsrebb   iccssxr     moved from FL's mathbox to main set.mm; revised
 7-Jul-14 iooirrsa  ioossre     moved from FL's mathbox to main set.mm; revised
 7-Jul-14 elicore2  icossre     moved from FL's mathbox to main set.mm
 7-Jul-14 elicore   icossxr     moved from FL's mathbox to main set.mm; revised
 7-Jul-14 eliocreb2 iocssre     moved from FL's mathbox to main set.mm
 7-Jul-14 eliocreb  iocssxr     moved from FL's mathbox to main set.mm; revised
 7-Jul-14 eliccre2b iccssre     moved from FL's mathbox to main set.mm
 7-Jul-14 eliccreb  iccssxr     moved from FL's mathbox to main set.mm; revised
 7-Jul-14 islvecd   ---         deleted; see islmodd and islvec2
 7-Jul-14 islmodd   [--same--]  revised
 7-Jul-14 islmod    [--same--]  revised
 7-Jul-14 df-lmod   [--same--]  revised (change g e. Abel to g e. Grp)
 7-Jul-14 fsump1i   [--same--]  revised
 7-Jul-14 difxp     [--same--]  revised
 2-Jul-14 difeq12   [--same--]  moved from FL's mathbox to main set.mm
 2-Jul-14 rngneg1   rngnegl     revised
 1-Jul-14 abl4pnp   ablo4pnp    (in JM's mathbox)
 1-Jul-14 ablinvop  abloinvop   (in JM's mathbox)
 1-Jul-14 ablcomgrp ablocomgrp  (in JM's mathbox)
 1-Jul-14 hhssabl   hhssablo
 1-Jul-14 hhssabli  hhssabloi
 1-Jul-14 hilabl    hilablo
 1-Jul-14 nvabl     nvablo
 1-Jul-14 vcabl     vcablo
 1-Jul-14 ablmul    ablomul
 1-Jul-14 ablsn     ablosn
 1-Jul-14 subgabl   subgablo
 1-Jul-14 isablda   isabloda
 1-Jul-14 ablnnncan1 ablonnncan1
 1-Jul-14 ablnncan  ablonncan
 1-Jul-14 ablnnncan ablonnncan
 1-Jul-14 abldivdiv4 ablodivdiv4
 1-Jul-14 abldivdiv ablodivdiv
 1-Jul-14 ablmuldiv ablomuldiv
 1-Jul-14 cabl      cablo
24-Jun-14 df-lmod   [--same--]  revised, and all affected definitions and
                                theorems were revised accordingly (156
                                statements in main set.mm, 4 in FL's mathbox,
                                257 in NM's mathbox, 417 total)
23-Jun-14 ---       ---         moved from JM's mathbox to main set.mm:
                                cphtpy cphtpc phtpy phtpyfval phtpyval isphtpy
                                phtpycom phtpyid phtpyco phtpc phtpcval
                                phtpcrel isphtpc phtpcdm phtpcer reparphti
                                reparpht cpi1b cpco cpi1 pco pi1b pi1 pcofval
                                pcoval pcovalg pcoval1 pco0 pco1 pcoval2 pcocn
                                pcoloopf pcohtpylem pcohtpy pcopt pcoass
                                pcorevlem pcorev pi1bval elpi1 elpi1i pi1bvalqs
                                pi1fval pi1flem pi1f pi1val pi1gplem pi1gp
                                pi1set
23-Jun-14 isablod   [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 isablda   [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 isgrpod   [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 isgrpda   [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 cnmpt2pc  [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 paste     [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 ---       ---         moved from JM's mathbox to main set.mm:
                                iccsplit iccshftr iccshftri iccshftl iccshftli
                                iccdil iccdili icccntr icccntri cii ii iitop
                                iiuni dfii2 dfii3 iicmp cnmptre iirev iirevcn
                                iihalf1 iihalf1cn iihalf2 iihalf2cn elii1 elii2
                                iimulcl iimulcn iccst icoopnst iocopnst
                                lincmb01cmp lincmb01icc oprpiece1res1
                                oprpiece1res2
23-Jun-14 subspcld2 [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 subspcld  [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 eroprf2   [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 erov2     [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 eroprf    [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 erov      [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 eroveu    [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 erovlem   [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 ecelqsg   [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 erthdmg   [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 oprabrexex2 [--same--] moved from JM's mathbox to main set.mm
23-Jun-14 oprabvalg ovg         moved from JM's mathbox to main set.mm

23-Jun-14 ---       ---         moved from SF's mathbox to main set.mm:
                                gcdmultiple rprimemulgcd rprimelpwr rprimepwr
                                gcd12 gcddiv gcdmultiplez dvdssqim sqgcd
                                dvdssqlem dvdssq divgcdodd gcdadd pythagtrip
                                trirecip
23-Jun-14 dvdsgcdid ---         (in SF's mathbox) deleted; see gcdeq
23-Jun-14 dvdsprime [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 ---       ---         moved from SF's mathbox to main set.mm:
                                gcdabs1 gcdabs2 dvdsgcdb gcdass mulgcdr
                                coprimeprodsq coprimeprodsq2 odd2np1lem odd2np1
                                opoe omoe opeo omeo
23-Jun-14 abssq     [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 zsqcl     [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 sqrlt     [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 nnsqcl    [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 1elunit   [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 0elunit   [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 binom2subi [--same--] moved from SF's mathbox to main set.mm
23-Jun-14 binom2sub [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 elicc2i   [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 preq12bg  [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 bfplem    bfplem2     (in JM's mathbox)
23-Jun-14 stioo     [--same--]  moved from JM's mathbox to main set.mm
23-Jun-14 elrege0   [--same--]  moved from SF's mathbox to main set.mm
23-Jun-14 clint3OLD icccld
23-Jun-14 eltop2    [--same--]  revised
23-Jun-14 ivthlem   ivthlem3
23-Jun-14 difreicc  [--same--]  revised
23-Jun-14 imaiun    imauni
16-Jun-14 icccmp    icccmpALT   (in JM's mathbox)
16-Jun-14 compfipin0 cmpfi      moved from JGH's mathbox to main set.mm
16-Jun-14 compfipin0lem cmpfilem moved from JGH's mathbox to main set.mm
16-Jun-14 hscptsscld hauscmp    moved from JGH's mathbox to main set.mm
16-Jun-14 hscptsscldlem hauscmplem moved from JGH's mathbox to main set.mm
16-Jun-14 uncomp    uncmp       moved from JGH's mathbox to main set.mm
16-Jun-14 cptclsscpt cmpcld     moved from JGH's mathbox to main set.mm
16-Jun-14 compsub   cmpsub      moved from JGH's mathbox to main set.mm
16-Jun-14 compsublem cmpsublem  moved from JGH's mathbox to main set.mm
16-Jun-14 compcov   cmpcov      moved from JGH's mathbox to main set.mm
16-Jun-14 comptop   cmptop      moved from JGH's mathbox to main set.mm
16-Jun-14 opncldf3  [--same--]  moved from JGH's mathbox to main set.mm
16-Jun-14 opncldf2  [--same--]  moved from JGH's mathbox to main set.mm
16-Jun-14 opncldf1  [--same--]  moved from JGH's mathbox to main set.mm
16-Jun-14 icc0      [--same--]  moved from FL's mathbox to main set.mm
16-Jun-14 ioc0      [--same--]  moved from FL's mathbox to main set.mm
16-Jun-14 ico0      [--same--]  moved from FL's mathbox to main set.mm
16-Jun-14 lbico1    [--same--]  moved from FL's mathbox to main set.mm
16-Jun-14 ubioc1    [--same--]  moved from FL's mathbox to main set.mm
16-Jun-14 cmptop    [--same--]  moved from FL's mathbox to main set.mm
16-Jun-14 sinempcomp 0cmp       moved from FL's mathbox to main set.mm
16-Jun-14 sbincgt   tgfiss      moved from FL's mathbox to main set.mm
16-Jun-14 neffopo   fiinopn     moved from FL's mathbox to main set.mm
16-Jun-14 rnxpid    [--same--]  moved from FL's mathbox to main set.mm
16-Jun-14 mayete3OLDi mayete3iOLD
16-Jun-14 df-toset  df-ts
16-Jun-14 ccha      ctsr
16-Jun-14 fintopcomp fincmp
16-Jun-14 comptoppr cmptoppr
16-Jun-14 cncomp    cncmp
16-Jun-14 iscomp    iscmp
16-Jun-14 df-comp   df-cmp
16-Jun-14 ccomp     ccmp
16-Jun-14 subbas2   ---         deleted; see fiuni
16-Jun-14 subbas    ---         deleted; see fibas
16-Jun-14 invrrOLD  ---         deleted; see drnginvrr
16-Jun-14 invrlOLD  ---         deleted; see drnginvrl
16-Jun-14 invrclOLD invrcllem
16-Jun-14 isumcmpss isumless
16-Jun-14 isumcmp   isumle
16-Jun-14 fsumtscop [--same--]  revised
16-Jun-14 fsumcmp   fsumle
16-Jun-14 fsumcmpss fsumless
16-Jun-14 isercmp   iserle
16-Jun-14 climcmpc2 climlec2
16-Jun-14 climcmp   climle
16-Jun-14 sercmp    serle
16-Jun-14 serdistr  seqdistr
16-Jun-14 serf1o    seqf1o
16-Jun-14 serf1olem2 seqf1olem2
16-Jun-14 serf1olem1 seqf1olem1
16-Jun-14 sercaopr  seqcaopr
16-Jun-14 sercaopr2 seqcaopr2
16-Jun-14 ioojoin   [--same--]  revised
16-Jun-14 snunioo   [--same--]  revised
16-Jun-14 snunioolem ---        deleted
16-Jun-14 icoun     [--same--]  revised
16-Jun-14 icounlem  ---         deleted
16-Jun-14 elico2    [--same--]  revised
16-Jun-14 elioc2    [--same--]  revised
16-Jun-14 elixx2    ---         deleted; see elioo2, elico2, elioc2, elicc2
16-Jun-14 ixxssicc  ixxssixx    revised
16-Jun-14 uzwo3lem2 ---         deleted
16-Jun-14 uzwo3lem1 ---         deleted
16-Jun-14 uzwo5OLD  ---         deleted
16-Jun-14 uzwo4OLD  ---         deleted
16-Jun-14 fmptd     [--same--]  revised
15-Jun-14 pwtr      [--same--]  moved from AS's mathbox to main set.mm; revised
15-Jun-14 pwtrr     pwtr        moved from AS's mathbox to main set.mm; revised
12-Jun-14 eroprv2   erov2       (in JM's mathbox)
12-Jun-14 eroprv    erov        (in JM's mathbox)
12-Jun-14 eropreu   eroveu      (in JM's mathbox)
12-Jun-14 eroprlem  erovlem     (in JM's mathbox)
12-Jun-14 eloprvdm2 elovdm2     (in JM's mathbox)
12-Jun-14 eloprvdm  elovdm      (in JM's mathbox)
12-Jun-14 oprabval4gc ov4gc     (in FL's mathbox)
12-Jun-14 oprabval2gc ov2gc     (in FL's mathbox)
12-Jun-14 opreq123i oveq123i    (in FL's mathbox)
12-Jun-14 fnoprvrn2 fnovrn2     (in FL's mathbox)
12-Jun-14 fnoprvpop fnovpop     (in FL's mathbox)
12-Jun-14 oprssoprvg oprssopvg  (in FL's mathbox)
12-Jun-14 symgoprv  symgov
12-Jun-14 subgopr   subgov
12-Jun-14 ecoprdi   ecovdi
12-Jun-14 ecoprass  ecovass
12-Jun-14 ecoprcom  ecovcom
12-Jun-14 oprec     ovec
12-Jun-14 eceqopreq eceqoveq
12-Jun-14 ecopoprer ecopover
12-Jun-14 ecopoprtrn ecopovtrn
12-Jun-14 ecopoprsym ecopovsym
12-Jun-14 ecopoprdm ecopovdm
12-Jun-14 ecopopreq ecopoveq
12-Jun-14 onopriun  onoviun
12-Jun-14 onopruni  onovuni
12-Jun-14 fnopr2v   fnov2
12-Jun-14 caoprmo   caovmo
12-Jun-14 caoprlem2 caovlem2
12-Jun-14 caoprdilem caovdilem
12-Jun-14 caoprdistrr caovdistrr
12-Jun-14 caopr42   caov42
12-Jun-14 caopr411  caov411
12-Jun-14 caopr4    caov4
12-Jun-14 caopr13   caov13
12-Jun-14 caopr31   caov31
12-Jun-14 caopr12   caov12
12-Jun-14 caopr32   caov32
12-Jun-14 caoprdistr caovdistr
12-Jun-14 caoprdistrg caovdistrg
12-Jun-14 caoprord3 caovord3
12-Jun-14 caoprord2 caovord2
12-Jun-14 caoprord  caovord
12-Jun-14 caoprcan  caovcan
12-Jun-14 caoprass  caovass
12-Jun-14 caoprassg caovassg
12-Jun-14 caoprcom  caovcom
12-Jun-14 caoprcomg caovcomg
12-Jun-14 caoprcl   caovcl
12-Jun-14 caoprcld  caovcld
12-Jun-14 ndmordi   ndmovordi
12-Jun-14 ndmord    ndmovord
12-Jun-14 ndmoprdistr ndmovdistr
12-Jun-14 ndmoprass ndmovass
12-Jun-14 ndmoprcom ndmovcom
12-Jun-14 ndmoprrcl ndmovrcl
12-Jun-14 ndmopr    ndmov
12-Jun-14 ndmoprcl  ndmovcl
12-Jun-14 ndmoprg   ndmovg
12-Jun-14 oprvconst2 ovconst2
12-Jun-14 oprelimab ovelimab
12-Jun-14 funimass4b funimassov
12-Jun-14 oprvelrn  ovelrn
12-Jun-14 fnoprvrn  fnovrn
12-Jun-14 fooprv    foov
12-Jun-14 fnrnoprv  fnrnov
12-Jun-14 foprrn    fovrn
12-Jun-14 oprssoprv oprssov
12-Jun-14 oprvres   ovres
12-Jun-14 oprabval6g ov6g
12-Jun-14 oprabval4gALT ov4gALT
12-Jun-14 oprabval4g ov4g
12-Jun-14 oprabval3 ov3
12-Jun-14 oprabval5 ov5
12-Jun-14 oprabval2 ov2
12-Jun-14 oprabval2g ov2g
12-Jun-14 oprabval2ag ov2ag
12-Jun-14 oprabval2gf ov2gf
12-Jun-14 oprabvalig ovig
12-Jun-14 oprabvaligg ovigg
12-Jun-14 oprabval  ov
12-Jun-14 foprv     fov
12-Jun-14 fnoprv    fnov
12-Jun-14 eqfnoprv2 eqfnov2
12-Jun-14 eqfnoprv  eqfnov
12-Jun-14 foprcl    fovcl
12-Jun-14 ffnoprv   ffnov
12-Jun-14 elimdeloprv elimdelov
12-Jun-14 fnotoprb  fnopovb
12-Jun-14 rcla4eopr rcla4eov
12-Jun-14 csbopr2g  csbov2g
12-Jun-14 csbopr1g  csbov1g
12-Jun-14 csbopr12g csbov12g
12-Jun-14 csboprg   csbovg
12-Jun-14 oprprc2   ovprc2
12-Jun-14 oprprc1   ovprc1
12-Jun-14 oprex     ovex
12-Jun-14 hboprd    hbovd
12-Jun-14 hbopr     hbov
12-Jun-14 opreq123d oveq123d
12-Jun-14 opreqan12rd oveqan12rd
12-Jun-14 opreqan12d oveqan12d
12-Jun-14 opreq12d  oveq12d
12-Jun-14 opreqd    oveqd
12-Jun-14 opreq2d   oveq2d
12-Jun-14 opreq1d   oveq1d
12-Jun-14 opreqi    oveqi
12-Jun-14 opreq12i  oveq12i
12-Jun-14 opreq2i   oveq2i
12-Jun-14 opreq1i   oveq1i
12-Jun-14 opreq12   oveq12
12-Jun-14 opreq2    oveq2
12-Jun-14 opreq1    oveq1
12-Jun-14 opreq     oveq
12-Jun-14 df-opr    df-ov
11-Jun-14 pi1val    [--same--]  (in JM's mathbox) revised
11-Jun-14 pi1f      [--same--]  (in JM's mathbox) revised
11-Jun-14 pi1fval   [--same--]  (in JM's mathbox) revised
11-Jun-14 pi1bvalqs [--same--]  (in JM's mathbox) revised
11-Jun-14 pcorev    [--same--]  (in JM's mathbox) revised
11-Jun-14 pcorevlem [--same--]  (in JM's mathbox) revised
11-Jun-14 pcoass    [--same--]  (in JM's mathbox) revised
11-Jun-14 pcohtpy   [--same--]  (in JM's mathbox) revised
11-Jun-14 ---       ---         pcohtpylem1 - pcohtpylem3 deleted
11-Jun-14 pco1      [--same--]  (in JM's mathbox) revised
11-Jun-14 pco0      [--same--]  (in JM's mathbox) revised
11-Jun-14 pcocn     [--same--]  (in JM's mathbox) revised
11-Jun-14 pcoval2   [--same--]  (in JM's mathbox) revised
11-Jun-14 pcoval1   [--same--]  (in JM's mathbox) revised
11-Jun-14 pcoval    [--same--]  (in JM's mathbox) revised
11-Jun-14 pcofval   [--same--]  (in JM's mathbox) revised
11-Jun-14 df-pco    [--same--]  (in JM's mathbox) revised
11-Jun-14 reparpht  [--same--]  (in JM's mathbox) revised
11-Jun-14 ---       ---         reparphtlem1 - reparphtlem2 deleted
11-Jun-14 isphtpc2  ---         (in JM's mathbox) deleted; see isphtpc
11-Jun-14 isphtpc   [--same--]  (in JM's mathbox) revised
11-Jun-14 df-phtpc  [--same--]  (in JM's mathbox) revised
11-Jun-14 phtpyco   [--same--]  (in JM's mathbox) revised
11-Jun-14 ---       ---         phtpycolem1 - phtpycolem5 deleted
11-Jun-14 phtpycom  [--same--]  (in JM's mathbox) revised
11-Jun-14 phtpyid   [--same--]  (in JM's mathbox) revised
11-Jun-14 isphtpy   [--same--]  (in JM's mathbox) revised
11-Jun-14 phtpyval  [--same--]  (in JM's mathbox) revised
11-Jun-14 phtpyfval [--same--]  (in JM's mathbox) revised
11-Jun-14 df-phtpy  [--same--]  (in JM's mathbox) revised
11-Jun-14 ismrer1   [--same--]  (in JM's mathbox) revised
11-Jun-14 rrnval    [--same--]  (in JM's mathbox) revised
11-Jun-14 df-rrn    [--same--]  (in JM's mathbox) revised
11-Jun-14 bfp       [--same--]  (in JM's mathbox) revised
11-Jun-14 ---       ---         bfplem1 - bfplem11 deleted
11-Jun-14 heiborlem8 [--same--] (in JM's mathbox) revised
11-Jun-14 heibor1lem [--same--] (in JM's mathbox) revised
11-Jun-14 mulcntx   mulcn       moved from JM's mathbox to main set.mm
11-Jun-14 subcntx   subcn       moved from JM's mathbox to main set.mm
11-Jun-14 addcntx   addcn       moved from JM's mathbox to main set.mm
11-Jun-14 txcc      [--same--]  moved from JM's mathbox to main set.mm; revised
11-Jun-14 txmet     [--same--]  moved from JM's mathbox to main set.mm; revised
11-Jun-14 cnoprab2c ---         (in JM's mathbox) deleted; see cnmpt2nd,cnmpt21
11-Jun-14 cnoprab1c ---         (in JM's mathbox) deleted; see cnmpt1st,cnmpt21
11-Jun-14 cnoprab2  ---         (in JM's mathbox) deleted; see cnmpt2nd,cnmpt21
11-Jun-14 cnoprab1  ---         (in JM's mathbox) deleted; see cnmpt1st,cnmpt21
11-Jun-14 cnoproprabcoc ---     (in JM's mathbox) deleted; see cnmpt22f
11-Jun-14 cnoproprabco ---      (in JM's mathbox) deleted; see cnmpt22f
11-Jun-14 cnopropabcoc ---      (in JM's mathbox) deleted; see cnmpt12f
11-Jun-14 cnopropabco ---       (in JM's mathbox) deleted; see cnmpt12f
11-Jun-14 cnresoprab2 ---       (in JM's mathbox) deleted; see cnmpt2res
11-Jun-14 cnresoprab ---        (in JM's mathbox) deleted; see cnmpt2res
11-Jun-14 txsubsp   [--same--]  moved from JM's mathbox to main set.mm
11-Jun-14 txcnoprab ---         (in JM's mathbox) deleted; see cnmpt2t
11-Jun-14 lmtlm     ---         (in JM's mathbox) deleted
11-Jun-14 tlmconst  ---         (in JM's mathbox) deleted; see lmconst
11-Jun-14 haustlmu  ---         (in JM's mathbox) deleted; see lmmo
11-Jun-14 tlmbrf    ---         (in JM's mathbox) deleted; see lmbrf
11-Jun-14 tlmbr     ---         (in JM's mathbox) deleted; see lmbr
11-Jun-14 tlmval    ---         (in JM's mathbox) deleted; see lmfval
11-Jun-14 df-tlm    ---         (in JM's mathbox) deleted; see df-lm
11-Jun-14 ctlm      ---         (in JM's mathbox) deleted
11-Jun-14 hmeocnv   ---         (in JM's mathbox) deleted; see cnvhmpha
11-Jun-14 hmeocn    ---         (in JM's mathbox) deleted; see hmeobc
11-Jun-14 ishomeo2  ishomeo     moved from JM's mathbox to main set.mm
11-Jun-14 piececn   cnmpt2pc    (in JM's mathbox) revised
11-Jun-14 cnres     ---         (in JM's mathbox) deleted; see cnsubsp
11-Jun-14 cnimass   ---         (in JM's mathbox) deleted; see cnsubsp2
11-Jun-14 cncfco    [--same--]  moved from JM's mathbox to main set.mm; revised
11-Jun-14 metdcn    [--same--]  moved from JM's mathbox to main set.mm; revised
11-Jun-14 caures    [--same--]  moved from JM's mathbox to main set.mm; revised
11-Jun-14 caushft   [--same--]  (in JM's mathbox) revised
11-Jun-14 lmclim2   [--same--]  (in JM's mathbox) revised
11-Jun-14 geomcau   [--same--]  (in JM's mathbox) revised
11-Jun-14 mettrifi2 ---         (in JM's mathbox) deleted; see mettrifi
11-Jun-14 mettrifi  [--same--]  (in JM's mathbox) revised
11-Jun-14 csbrni    [--same--]  (in JM's mathbox) revised
11-Jun-14 trirni    ---         (in JM's mathbox) deleted; see isumshft
11-Jun-14 csbrni    csbrn       (in JM's mathbox) revised
11-Jun-14 fsumlt1   fsumge1     moved from JM's mathbox to main set.mm; revised
11-Jun-14 isumshft2 ---         (in JM's mathbox) deleted; see isumshft
11-Jun-14 iserzshft2 ---        (in JM's mathbox) deleted; see isershft
11-Jun-14 isumclf   ---         (in JM's mathbox) deleted; see isumcl
11-Jun-14 fsumleisum ---        (in JM's mathbox) deleted; see isumless
11-Jun-14 fsumleisumi ---       (in JM's mathbox) deleted; see isumless
11-Jun-14 fsumleisumii ---      (in JM's mathbox) deleted; see isumless
11-Jun-14 fsumltisum isumltss   moved from JM's mathbox to main set.mm; revised
11-Jun-14 fsumltisumi ---       (in JM's mathbox) deleted; see isumltss
11-Jun-14 fsumltisumii ---      (in JM's mathbox) deleted; see isumltss
11-Jun-14 fsumlt    [--same--]  moved from JM's mathbox to main set.mm; revised
11-Jun-14 fsum00OLD ---         (in JM's mathbox) deleted
11-Jun-14 seq1eq2   ---         (in JM's mathbox) deleted; see seqfveq
11-Jun-14 sdc       [--same--]  (in JM's mathbox) revised
11-Jun-14 sdclem2   [--same--]  (in JM's mathbox) revised
11-Jun-14 sdclem1   [--same--]  (in JM's mathbox) revised
11-Jun-14 seq1seqzgOLD ---      (in JM's mathbox) deleted
11-Jun-14 seqzp1gOLD ---        (in JM's mathbox) deleted
11-Jun-14 seqz1gOLD ---         (in JM's mathbox) deleted
11-Jun-14 seq1p1gOLD ---        (in JM's mathbox) deleted
11-Jun-14 seq11gOLD ---         (in JM's mathbox) deleted
11-Jun-14 divexp    expdiv      moved from JM's mathbox to main set.mm; revised
11-Jun-14 acdc5g    ---         (in JM's mathbox) deleted; see axdc4uz
11-Jun-14 acdc3g    ---         (in JM's mathbox) deleted; see axdc3
11-Jun-14 acdcg     ---         (in JM's mathbox) deleted; see axdc2
11-Jun-14 hbixp1    [--same--]  moved from JM's mathbox to main set.mm
11-Jun-14 cbvixpv   [--same--]  moved from JM's mathbox to main set.mm
11-Jun-14 cbvixp    [--same--]  moved from JM's mathbox to main set.mm
11-Jun-14 cnsubsp2  [--same--]  moved from JGH's mathbox to main set.mm
11-Jun-14 cnsubsp   [--same--]  moved from JGH's mathbox to main set.mm
11-Jun-14 avgle2    [--same--]  moved from JGH's mathbox to main set.mm
11-Jun-14 cntrsetlem ---        (in FL's mathbox) deleted
11-Jun-14 topgrpsubcnlem ---    (in FL's mathbox) deleted
11-Jun-14 exopcopn  [--same--]  (in FL's mathbox) revised
11-Jun-14 ttcn2     ---         (in FL's mathbox) deleted; see cnmpt1t
11-Jun-14 ttcn      ---         (in FL's mathbox) deleted; see cnmpt1t
11-Jun-14 eltpt     [--same--]  moved from FL's mathbox to main set.mm
11-Jun-14 eqindhome [--same--]  (in FL's mathbox) revised
11-Jun-14 hmeogrp   [--same--]  (in FL's mathbox) revised
11-Jun-14 rnhmpha   [--same--]  (in FL's mathbox) revised
11-Jun-14 dmhmpha   [--same--]  (in FL's mathbox) revised
11-Jun-14 cnvhmphb  ---         (in FL's mathbox) deleted; see cnvhmph
11-Jun-14 df-mmat   [--same--]  (in FL's mathbox) revised
11-Jun-14 df-expsg  [--same--]  (in FL's mathbox) revised
11-Jun-14 seqzp2    [--same--]  (in FL's mathbox) revised
11-Jun-14 isppm     [--same--]  (in FL's mathbox) revised
11-Jun-14 fprod1ib  fprod2      (in FL's mathbox) revised
11-Jun-14 fprod1i2  ---         (in FL's mathbox) deleted; see fprod1i
11-Jun-14 relsumprd fsumprd     (in FL's mathbox) revised
11-Jun-14 fprodp1s1 ---         (in FL's mathbox) deleted; see fprodp1s
11-Jun-14 fprodp1s1 ---         (in FL's mathbox) deleted; see fprodp1s
11-Jun-14 fprodp1s  [--same--]  (in FL's mathbox) revised
11-Jun-14 fprodp1slem ---       (in FL's mathbox) deleted
11-Jun-14 fprodp1fi [--same--]  (in FL's mathbox) revised
11-Jun-14 fprod1s1  ---         (in FL's mathbox) deleted; see fprod1s
11-Jun-14 fprod1s2  fprod1s     (in FL's mathbox) revised
11-Jun-14 fprod1slem ---        (in FL's mathbox) deleted
11-Jun-14 fprod1fi  [--same--]  (in FL's mathbox) revised
11-Jun-14 fprodp1i  [--same--]  (in FL's mathbox) revised
11-Jun-14 fprod1i   [--same--]  (in FL's mathbox) revised
11-Jun-14 fprodserzfi fprodserf (in FL's mathbox) revised
11-Jun-14 fprodserz fprodser    (in FL's mathbox) revised
11-Jun-14 dffprod   [--same--]  (in FL's mathbox) revised
11-Jun-14 prodeqfv  [--same--]  (in FL's mathbox) revised
11-Jun-14 prodeq3d  [--same--]  (in FL's mathbox) revised
11-Jun-14 prodeq123d [--same--] (in FL's mathbox) revised
11-Jun-14 prodeq123i [--same--] (in FL's mathbox) revised
11-Jun-14 prodeq3   prodeq2     (in FL's mathbox) (these labels should be
11-Jun-14 prodeq2   prodeq3     (in FL's mathbox)  exchanged at the same time)
11-Jun-14 valproemset prod0     (in FL's mathbox)
11-Jun-14 df-prod2  ---         (in FL's mathbox) deleted; see df-prod
11-Jun-14 df-prod   [--same--]  (in FL's mathbox) revised
11-Jun-14 cprd2     ---         (in FL's mathbox) deleted
11-Jun-14 cprd      [--same--]  (in FL's mathbox) revised
11-Jun-14 seq0p1g   ---         (in FL's mathbox) deleted; see seqp1
11-Jun-14 seq00g    ---         (in FL's mathbox) deleted; see seq1
11-Jun-14 iserzmulc1b ---       (in FL's mathbox) deleted; see isermulc2
11-Jun-14 prjnpl    resixp      moved from FL's mathbox to main set.mm
11-Jun-14 cbicp     [--same--]  (in FL's mathbox) revised
11-Jun-14 cbicplem  ---         (in FL's mathbox) deleted
11-Jun-14 isprj2    [--same--]  (in FL's mathbox) revised
11-Jun-14 isprj1    [--same--]  (in FL's mathbox) revised
11-Jun-14 hbcp      ---         (in FL's mathbox) deleted; see hbixp1
11-Jun-14 valpr     [--same--]  (in FL's mathbox) changed variable names
11-Jun-14 prmapcp3  ---         (in FL's mathbox) deleted; see prmapcp2
11-Jun-14 prmapcp2  [--same--]  (in FL's mathbox) changed variable names
11-Jun-14 ispr1     [--same--]  (in FL's mathbox) revised
11-Jun-14 df-prj    [--same--]  (in FL's mathbox) revised
11-Jun-14 df-pro    [--same--]  (in FL's mathbox) revised
11-Jun-14 dffn5b    ---         (in FL's mathbox) deleted; see dffn5v
11-Jun-14 fopabco3  fmptco      moved from FL's mathbox to main set.mm
11-Jun-14 riemtn    ---         (in FL's mathbox) deleted; see mptresid
11-Jun-14 riecb     ---         (in FL's mathbox) deleted; see opabresid
11-Jun-14 cmpran    ---         (in FL's mathbox) deleted; see rnmpt
11-Jun-14 fopab2a   ---         (in FL's mathbox) deleted; see fmpt
11-Jun-14 fopab2ga  ---         (in FL's mathbox) deleted; see fnmpt
11-Jun-14 cmpbvb    ---         (in FL's mathbox) deleted; see cbvmptv
11-Jun-14 fmptb     ---         (in FL's mathbox) deleted; see fmpt2
11-Jun-14 seq0clg   ---         (in FL's mathbox) deleted; see seqcl
11-Jun-14 bpolydiflem2 ---      (in SF's mathbox) deleted
11-Jun-14 bpolydiflem1 ---      (in SF's mathbox) deleted
11-Jun-14 bernpolycl bpolycl    (in SF's mathbox)
11-Jun-14 bernpoly1 bpoly1      (in SF's mathbox)
11-Jun-14 bernpolynn ---        (in SF's mathbox) deleted; see bpolyval
11-Jun-14 bernpoly0 bpoly0      (in SF's mathbox)
11-Jun-14 bernpolyval bpolyval  (in SF's mathbox) revised
11-Jun-14 df-bernpoly df-bpoly  (in SF's mathbox) revised
11-Jun-14 cbernpoly cbp         (in SF's mathbox)
11-Jun-14 fsumsq    ---         (in SF's mathbox) deleted; see fsumge0
11-Jun-14 trirecip  [--same--]  (in SF's mathbox) revised
11-Jun-14 trireciplem [--same--] (in SF's mathbox) revised
11-Jun-14 arisum4   ---         (in SF's mathbox) deleted; see arisum
11-Jun-14 arisum3   ---         (in SF's mathbox) deleted; see arisum
11-Jun-14 arisum2   ---         (in SF's mathbox) deleted; see arisum
11-Jun-14 arisum    [--same--]  moved from SF's mathbox to main set.mm; revised
11-Jun-14 binomp1m1 [--same--]  moved from SF's mathbox to main set.mm
11-Jun-14 binom21   [--same--]  moved from SF's mathbox to main set.mm
11-Jun-14 binom1dif [--same--]  moved from SF's mathbox to main set.mm
11-Jun-14 binom1    ---         (in SF's mathbox) deleted; see binom1p
11-Jun-14 binom     [--same--]  moved from SF's mathbox to main set.mm
11-Jun-14 bcsum     ---         (in SF's mathbox) deleted; see binom11
11-Jun-14 fsumtelescope2 fsumtscop moved from SF's mathbox to main set.mm
11-Jun-14 fsumtelescope ---     (in SF's mathbox) deleted; see fsumtscop
11-Jun-14 fsumsplitlast ---     (in SF's mathbox) deleted; see fsump1
11-Jun-14 fseq1cl   ---         (in PC's mathbox) deleted; see seqcl
11-Jun-14 seq1resval2 ---       (in PC's mathbox) deleted; see seqfveq
11-Jun-14 seq1resval ---        (in PC's mathbox) deleted; see seqfveq
11-Jun-14 seqzresval2 ---       (in PC's mathbox) deleted; see seqfveq
11-Jun-14 ---       ---         circumlem1 - circumlem3 deleted
11-Jun-14 sindivcvg sinccvg     (in PC's mathbox)
11-Jun-14 ---       ---         sindivcvglem1 - sindivcvglem8 deleted
11-Jun-14 efexple   [--same--]  (in MC's mathbox) revised
11-Jun-14 bclbnd2   bclbnd      (in MC's mathbox)
11-Jun-14 bclbnd    ---         (in MC's mathbox) deleted
11-Jun-14 elpjrnch  elpjch
11-Jun-14 elpjch    [--same--]  revised
11-Jun-14 pjhmopidm [--same--]  revised
11-Jun-14 hmopidmpj [--same--]  revised
11-Jun-14 hmopidmch [--same--]  revised
11-Jun-14 hmopidmpji [--same--] revised
11-Jun-14 hmopidmchi [--same--] revised
11-Jun-14 hmopidmchlem ---      deleted
11-Jun-14 opsqrlem6 [--same--]  revised
11-Jun-14 opsqrlem5 [--same--]  revised
11-Jun-14 opsqrlem4 [--same--]  revised
11-Jun-14 opsqrlem3 [--same--]  revised
11-Jun-14 opsqrlem2 [--same--]  revised
11-Jun-14 chso      pjth
11-Jun-14 ---       ---         osumlem1 - osumlem8 deleted
11-Jun-14 pjtheu2i  pjtheu2     revised
11-Jun-14 pjeq2     ---         deleted; see pjeq
11-Jun-14 pjtheui   ---         deleted; see pjtheu
11-Jun-14 pjth      [--same--]  revised
11-Jun-14 pjthi     ---         deleted; see pjth
11-Jun-14 ---       ---         pjthlem3 - pjthlem14 deleted
11-Jun-14 pjthlem2  [--same--]  revised
11-Jun-14 pjthlem1  [--same--]  revised
11-Jun-14 projlemHIL ---        deleted
11-Jun-14 projlem   ---         deleted
11-Jun-14 ---       ---         projlem1 - projlem31 deleted
11-Jun-14 occli     ---         deleted; see occl
11-Jun-14 ---       ---         occllem1 - occllem8 deleted
11-Jun-14 hlimeui   [--same--]  revised
11-Jun-14 hlimreui  [--same--]  revised
11-Jun-14 hlimuniii ---         deleted; see hlimunii
11-Jun-14 hlimcauii ---         deleted; see hlimcaui
11-Jun-14 hilcmpl   [--same--]  revised
11-Jun-14 hhcmpl    [--same--]  revised
11-Jun-14 hhlm      [--same--]  revised
11-Jun-14 hilcau    ---         deleted; see hhcau
11-Jun-14 hillim    ---         deleted; see hhlm
11-Jun-14 hlim2     [--same--]  revised
11-Jun-14 hlimconvi [--same--]  revised
11-Jun-14 hlimi     [--same--]  revised
11-Jun-14 hcau2     ---         deleted; see hcau
11-Jun-14 seq1hcau  [--same--]  revised
11-Jun-14 hcaucvg   [--same--]  revised
11-Jun-14 hcau      [--same--]  revised
11-Jun-14 h2hlm     [--same--]  revised
11-Jun-14 df-hcau   [--same--]  revised
11-Jun-14 df-hlim   [--same--]  revised
11-Jun-14 hmph      [--same--]  revised
11-Jun-14 hmeobc    [--same--]  revised
11-Jun-14 ishomeo   [--same--]  revised
11-Jun-14 df-hmph   [--same--]  revised
11-Jun-14 relogexp  [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 reexplog  [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 explog    [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 pilog     logm1       revised
11-Jun-14 resslogrn relogrn     revised
11-Jun-14 logrn     [--same--]  revised
11-Jun-14 df-log    [--same--]  revised
11-Jun-14 eff1o     [--same--]  revised
11-Jun-14 eff1oi    eff1olem    revised
11-Jun-14 effoi     ---         deleted; see eff1o
11-Jun-14 eff1i     ---         deleted; see eff1o
11-Jun-14 eff1lem   ---         deleted
11-Jun-14 shftefif1o ---        deleted; see efif1o
11-Jun-14 shftefif1olem ---     deleted
11-Jun-14 circgrp   [--same--]  revised
11-Jun-14 efielcirc ---         deleted
11-Jun-14 efif1o    [--same--]  revised
11-Jun-14 efif1     ---         deleted; see efif1o
11-Jun-14 ---       ---         efif1lem1 - efif1lem7 deleted
11-Jun-14 efifo     ---         deleted; see efif1o
11-Jun-14 ---       ---         efifolem1 - efifolem7 deleted
11-Jun-14 efif      ---         deleted; see efif1o
11-Jun-14 efghgrpi  efghgrp     revised
11-Jun-14 efghgrpilem ---       deleted
11-Jun-14 efgh      [--same--]  revised
11-Jun-14 cosh111   cos11       revised
11-Jun-14 ---       ---         cosh111lem1 - cosh111lem3 deleted
11-Jun-14 sineq0re  ---         deleted; see sineq0
11-Jun-14 sineq0OLD ---         deleted; see sineq0
11-Jun-14 sineq0    [--same--]  revised
11-Jun-14 sinq12gt0t sinq12gt0
11-Jun-14 sinperlem2 ---        deleted
11-Jun-14 sinperlem1 ---        deleted
11-Jun-14 pilem4    ---         deleted; see pilem3
11-Jun-14 pilem3    [--same--]  revised
11-Jun-14 pilem2    [--same--]  revised
11-Jun-14 pilem1    [--same--]  revised
11-Jun-14 cosco     ---         deleted
11-Jun-14 sinco     ---         deleted
11-Jun-14 sincnlem  ---         deleted
11-Jun-14 sincolem  ---         deleted
11-Jun-14 hlcompl   [--same--]  revised
11-Jun-14 minvecex2 ---         deleted; see minvec
11-Jun-14 minveclem39 ---       deleted
11-Jun-14 minvecle  ---         deleted; see minvec
11-Jun-14 minvecdist ---        deleted; see minvec
11-Jun-14 minveccl  ---         deleted; see minvec
11-Jun-14 minveceu   minvec     revised
11-Jun-14 ---       ---         minveclem35 - minveclem38 deleted
11-Jun-14 minvecex  ---         deleted; see minvec
11-Jun-14 ---       ---         minveclem10 - minveclem33 deleted
11-Jun-14 minvec34   ---        deleted
11-Jun-14 minveclem7 [--same--] revised
11-Jun-14 minveclem6 [--same--] revised
11-Jun-14 minveclem5 [--same--] revised
11-Jun-14 minveclem4 [--same--] revised
11-Jun-14 minveclem3 [--same--] revised
11-Jun-14 minveclem2 [--same--] revised
11-Jun-14 minveclem1 [--same--] revised
11-Jun-14 ipasslem7 [--same--]  revised
11-Jun-14 ipasslem6 ---         deleted
11-Jun-14 ip1cni    ---         deleted; see ipcn
11-Jun-14 ---       ---         ip1cnilem1 - ip1cnilem6 deleted
11-Jun-14 ipval2lem1 ---        deleted
11-Jun-14 sm1cni    ---         deleted; see smcn
11-Jun-14 sm1cnilem ---         deleted
11-Jun-14 va1cn     ---         deleted; see vacn and cnmpt12
11-Jun-14 va1cnlem  ---         deleted
11-Jun-14 vacn      [--same--]  revised
11-Jun-14 ---       ---         vacnlem1 - vacnlem6 deleted
11-Jun-14 nvlmle    [--same--]  revised
11-Jun-14 nvlmcl    [--same--]  revised
11-Jun-14 ghsubgi   ghsubg      revised
11-Jun-14 ghgrpi    ghgrp       revised
11-Jun-14 ---       ---         ghgrpilem1 - ghgrpilem4 deleted
11-Jun-14 bcthlem3  [--same--]  revised
11-Jun-14 cmsss     [--same--]  revised
11-Jun-14 lmcau     [--same--]  revised
11-Jun-14 iscms2i   iscms3i     revised
11-Jun-14 iscms2    iscms3      revised
11-Jun-14 ---       ---         iscms2lem3 - iscms2lem5 deleted
11-Jun-14 fsumcn    [--same--]  revised
11-Jun-14 fsumcnlem ---         deleted
11-Jun-14 mulcn     [--same--]  revised
11-Jun-14 subcn     [--same--]  revised
11-Jun-14 addcn     [--same--]  revised
11-Jun-14 bopcn     ---         deleted; see metcn4
11-Jun-14 ---       ---         bopcnlem1 - bopcnlem4 deleted
11-Jun-14 opr1scn   ---         deleted; see cnmpt12f and cnmptid, cnmptc
11-Jun-14 opr2cn    ---         deleted; see cnmpt12f and cnmptc
11-Jun-14 opr1cn    ---         deleted; see cnmpt12f and cnmptc
11-Jun-14 oprcn     ---         deleted; see cnmpt12f
11-Jun-14 xpcn      ---         deleted; see cnmpt1t
11-Jun-14 xplm      ---         deleted; see txlm
11-Jun-14 xplmi2    ---         deleted; see txlm
11-Jun-14 xplmi     ---         deleted; see txlm
11-Jun-14 metcnp4   [--same--]  revised
11-Jun-14 metcnp4lem2 ---       deleted
11-Jun-14 metcnp4lem1 ---       deleted
11-Jun-14 caublcls  [--same--]  revised
11-Jun-14 metcld    [--same--]  revised
11-Jun-14 metcls    ---         deleted; see metelcls
11-Jun-14 metelcls  [--same--]  revised
11-Jun-14 metcls2   ---         deleted; see lmcls
11-Jun-14 lmclimnn  lmclimf     revised
11-Jun-14 lmclim    [--same--]  revised
11-Jun-14 lmle      [--same--]  revised
11-Jun-14 lmfex     ---         deleted
11-Jun-14 lmfexlem3 ---         deleted
11-Jun-14 lmfexlem2 ---         deleted
11-Jun-14 lmfexlem1 ---         deleted
11-Jun-14 caussi    [--same--]  revised
11-Jun-14 lmss      [--same--]  revised
11-Jun-14 lmsslem   ---         deleted
11-Jun-14 lmuni     lmmo        revised
11-Jun-14 caufss    caufpm      revised
11-Jun-14 lmcl      [--same--]  revised
11-Jun-14 lmfss     [--same--]  revised
11-Jun-14 cmscvg    [--same--]  revised
11-Jun-14 iscms     [--same--]  revised
11-Jun-14 iscaunns  ---         deleted; see iscauf
11-Jun-14 lmcvgnns  ---         deleted; see lmmcvg
11-Jun-14 lmbrnns   ---         deleted; see iscauf
11-Jun-14 iscau5    ---         deleted; see iscauf
11-Jun-14 iscau4    [--same--]  revised
11-Jun-14 iscauf    [--same--]  revised
11-Jun-14 iscau3    [--same--]  revised
11-Jun-14 iscau2    [--same--]  revised
11-Jun-14 iscau     [--same--]  revised
11-Jun-14 lmnn      [--same--]  revised
11-Jun-14 lmconst   [--same--]  revised
11-Jun-14 lmcvg2    ---         deleted; see lmcvg
11-Jun-14 lmcvg     [--same--]  revised
11-Jun-14 lmbrf2    ---         deleted; see lmbrf
11-Jun-14 lmbrf     [--same--]  revised
11-Jun-14 lmbr2     [--same--]  revised
11-Jun-14 lmbr      [--same--]  revised
11-Jun-14 lmrel     [--same--]  revised
11-Jun-14 caufval   [--same--]  revised
11-Jun-14 lmfval    [--same--]  revised
11-Jun-14 df-cmet   [--same--]  revised
11-Jun-14 df-cau    [--same--]  revised
11-Jun-14 df-lm     [--same--]  revised
11-Jun-14 clm       [--same--]  revised
11-Jun-14 dscmet    [--same--]  revised
11-Jun-14 cn2met    [--same--]  revised
11-Jun-14 metdnsconst ---       deleted; see dnsconst
11-Jun-14 metxp     [--same--]  revised
11-Jun-14 metxplem4 [--same--]  revised
11-Jun-14 metxpcl   [--same--]  revised
11-Jun-14 metxpfval [--same--]  revised
11-Jun-14 metxptval [--same--]  revised
11-Jun-14 metxpdval [--same--]  revised
11-Jun-14 2txcn     ---         deleted; see cnmpt2t
11-Jun-14 txcnopab  txcnmpt     revised
11-Jun-14 txcn      [--same--]  revised
11-Jun-14 tx2cn     [--same--]  revised
11-Jun-14 tx1cn     [--same--]  revised
11-Jun-14 txcld     [--same--]  revised
11-Jun-14 txopn     [--same--]  revised
11-Jun-14 txuni     [--same--]  revised
11-Jun-14 txtop     [--same--]  revised
11-Jun-14 stoig2    [--same--]  revised
11-Jun-14 1arith2   [--same--]  revised
11-Jun-14 1arith    [--same--]  revised
11-Jun-14 ---       ---         1arithlem4 - 1arithlem31 deleted
11-Jun-14 1arithlem4 [--same--] revised
11-Jun-14 1arithlem3 [--same--] revised
11-Jun-14 1arithlem2 [--same--] revised
11-Jun-14 1arithlem1 [--same--] revised
11-Jun-14 ---       ---         mulgcdlem1 - mulgcdlem7 deleted
11-Jun-14 eucalg    [--same--]  revised
11-Jun-14 eucalgcvga [--same--] revised
11-Jun-14 eucalglt  [--same--]  revised
11-Jun-14 eucalginv [--same--]  revised
11-Jun-14 eucalgf   [--same--]  revised
11-Jun-14 eucalgval2 [--same--] revised
11-Jun-14 eucalgval [--same--]  revised
11-Jun-14 algfx     [--same--]  revised
11-Jun-14 algcvga   [--same--]  revised
11-Jun-14 algcvg    [--same--]  revised
11-Jun-14 alginv    [--same--]  revised
11-Jun-14 algrp1    [--same--]  revised
11-Jun-14 algrp1lem ---         deleted
11-Jun-14 algr0     [--same--]  revised
11-Jun-14 algrf     [--same--]  revised
11-Jun-14 ruclem39  ruclem13
11-Jun-14 ---       ---         ruclem13 - ruclem38 deleted
11-Jun-14 ruclem12  [--same--]  revised
11-Jun-14 ruclem11  [--same--]  revised
11-Jun-14 ruclem10  [--same--]  revised
11-Jun-14 ruclem9   [--same--]  revised
11-Jun-14 ruclem8   [--same--]  revised
11-Jun-14 ruclem7   [--same--]  revised
11-Jun-14 ruclem6   [--same--]  revised
11-Jun-14 ruclem5   [--same--]  revised
11-Jun-14 ruclem4   [--same--]  revised
11-Jun-14 ruclem3   [--same--]  revised
11-Jun-14 ruclem2   [--same--]  revised
11-Jun-14 ruclem1   [--same--]  revised
11-Jun-14 rpnnen2lem11 [--same--] revised
11-Jun-14 rpnnen2lem10 [--same--] revised
11-Jun-14 rpnnen2lem9 [--same--] revised
11-Jun-14 rpnnen2lem8 [--same--] revised
11-Jun-14 rpnnen2lem7 [--same--] revised
11-Jun-14 rpnnen2lem6 [--same--] revised
11-Jun-14 rpnnen2lem5 [--same--] revised
11-Jun-14 rpnnen2lem4 [--same--] revised
11-Jun-14 rpnnen2lem3 [--same--] revised
11-Jun-14 rpnnen2lem2 [--same--] revised
11-Jun-14 rpnnen2lem1 [--same--] revised
11-Jun-14 acdcALT   ---         deleted; see axdc2
11-Jun-14 acdc      ---         deleted; see axdc2
11-Jun-14 acdclem   ---         deleted
11-Jun-14 acdc5     ---         deleted; see axdc4
11-Jun-14 acdc5lem2 ---         deleted
11-Jun-14 acdc5lem1 ---         deleted
11-Jun-14 acdc2     ---         deleted; see axdc4
11-Jun-14 acdc2lem2 ---         deleted
11-Jun-14 acdc2lem1 ---         deleted
11-Jun-14 acdc4lem1 ---         deleted
11-Jun-14 acdc3     ---         deleted; see axdc3
11-Jun-14 acdc3lem  ---         deleted
11-Jun-14 demoivre  ---         generalized antecedent to N e. ZZ
11-Jun-14 ---       ---         cos01bndlem2 - cos01bndlem3 deleted
11-Jun-14 ---       ---         sin01bndlem1 - sin01bndlem3 deleted
11-Jun-14 cos2OLD   ---         deleted; see cos2t
11-Jun-14 subcos    [--same--]  revised
11-Jun-14 cosaddi   ---         deleted; see cosadd
11-Jun-14 sinaddi   ---         deleted; see sinadd
11-Jun-14 sin0ALT   ---         deleted; see sin0
11-Jun-14 efi4p     [--same--]  revised
11-Jun-14 reeff1olem2 ---       deleted
11-Jun-14 reeff1olem1 ---       deleted
11-Jun-14 ---       ---         efcnlem1 - efcnlem1 deleted
11-Jun-14 efm1legeo ---         deleted
11-Jun-14 efm1legeoi ---        deleted
11-Jun-14 eflegeo   [--same--]  revised
11-Jun-14 eflegeoi  ---         deleted
11-Jun-14 eflegeolem2 ---       deleted
11-Jun-14 eflegeolem1 ---       deleted
11-Jun-14 absefm1lei ---        deleted
11-Jun-14 efm1limi  ---         deleted
11-Jun-14 efltbi    ---         deleted; see eflt
11-Jun-14 eflti     [--same--]  revised
11-Jun-14 efgt0i    ---         deleted; see efgt0
11-Jun-14 efgt0i    ---         deleted; see efgt0
11-Jun-14 efgt1pi   efgt1p      revised
11-Jun-14 efgt1i    efgt1       revised
11-Jun-14 efge1pi   ---         deleted; see efgt1p
11-Jun-14 efge1i    ---         deleted; see efgt1
11-Jun-14 ef4p      [--same--]  revised
11-Jun-14 ef4pi     ---         deleted; see ef4p
11-Jun-14 eft0vali  eft0val     revised
11-Jun-14 effsumlei effsumlt    revised
11-Jun-14 efsepi    efsep       revised
11-Jun-14 abspef01tlubi ---     deleted; see eftlub
11-Jun-14 elt3OLD   ---         deleted; see egt2lt3
11-Jun-14 egt2OLD   ---         deleted; see egt2lt3
11-Jun-14 ---       ---         eirrlem1 - eirrlem5 deleted
11-Jun-14 absef01tlubi eftlub   revised
11-Jun-14 absef01tllem ---      deleted
11-Jun-14 ef01tlubi ---         deleted; see eftlub
11-Jun-14 ef01tllem2OLD ---     deleted
11-Jun-14 ef01tllem2 ---        deleted
11-Jun-14 ef01tllem1 ---        deleted
11-Jun-14 ef1tlubi  ---         deleted; see eftlub
11-Jun-14 ef1tllem  ---         deleted
11-Jun-14 reeftlcl  [--same--]  revised
11-Jun-14 eftlcl    [--same--]  revised
11-Jun-14 eftlex    eftlcvg     revised
11-Jun-14 eftlexiOLD ---        deleted
11-Jun-14 eftlubcl  ---         deleted
11-Jun-14 eftabsi   eftabs      revised
11-Jun-14 efnn0val  efzval      generalized antecedent to N e. ZZ
11-Jun-14 efexp     [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 efaddi    ---         deleted; see efadd
11-Jun-14 ---       ---         efaddlem1 - efaddlem28 deleted
11-Jun-14 efcji     ---         deleted; see efcj
11-Jun-14 ege2le3   [--same--]  revised; see egt2lt3
11-Jun-14 ele3      ---         deleted; see egt2lt3
11-Jun-14 ege2      ---         deleted; see egt2lt3
11-Jun-14 ereALT    ---         deleted; see ere
11-Jun-14 ege2le3lem2 ---       deleted
11-Jun-14 ege2lem2  ---         deleted
11-Jun-14 ege2le3lem1 ---       deleted
11-Jun-14 ele3lem   ---         deleted
11-Jun-14 ---       ---         erelem1 - erelem7 deleted
11-Jun-14 reefcli   ---         deleted; see reefcl
11-Jun-14 eftval    [--same--]  revised
11-Jun-14 efcvgfsum [--same--]  revised
11-Jun-14 efcvg     [--same--]  revised
11-Jun-14 efseq0ex  ---         deleted; see efcllem
11-Jun-14 ef0lem    [--same--]  revised
11-Jun-14 dfef2i    ---         deleted
11-Jun-14 efseq1ex  ---         deleted; see efcllem
11-Jun-14 efcltlem2 ---         deleted; see ef0lem
11-Jun-14 efcltlem1 ---         deleted; see efcllem
11-Jun-14 df-pi     [--same--]  revised
11-Jun-14 df-tan    [--same--]  revised
11-Jun-14 dsupivthi ivth2       revised
11-Jun-14 dsupivthlem ---       deleted
11-Jun-14 isupivthi ivth        revised
11-Jun-14 ---       ---         ivthlem1 - ivthlem9 deleted
11-Jun-14 divccncf  [--same--]  revised
11-Jun-14 mulc1cncf [--same--]  revised
11-Jun-14 abscncflem ---        deleted
11-Jun-14 negfcncfi negfcncf    revised
11-Jun-14 fsum0diag4 ---        deleted; see fsum0diag
11-Jun-14 fsum0diag3 ---        deleted; see fsum0diag
11-Jun-14 fsum0diag2 ---        deleted; see fsum0diag
11-Jun-14 fsum0diag [--same--]  revised
11-Jun-14 fsum0diaglem2 ---     deleted
11-Jun-14 fsum0diaglem1 ---     deleted
11-Jun-14 cvgrati   cvgrat      revised
11-Jun-14 ---       ---         cvgratlem1 - cvgratlem5 deleted
11-Jun-14 ---       ---         cvgratlem1ALT - cvgratlem3ALT deleted
11-Jun-14 geosum2i  ---         deleted; see geoser
11-Jun-14 geosumi   ---         deleted; see geoser
11-Jun-14 georeclim [--same--]  revised
11-Jun-14 geolim1   ---         deleted; see geolim2
11-Jun-14 geolim1i  ---         deleted; see geolim2
11-Jun-14 geolim    [--same--]  revised
11-Jun-14 geolimi   ---         deleted; see geolim
11-Jun-14 geolimilem ---        deleted
11-Jun-14 geoseri   geoser      revised
11-Jun-14 explecnv  [--same--]  revised
11-Jun-14 expcnv    [--same--]  revised
11-Jun-14 ---       ---         expcnvlem1 - expcnvlem6 deleted
11-Jun-14 arisumi   arisum      revised
11-Jun-14 arisumilem ---        deleted
11-Jun-14 supcvg    [--same--]  revised
11-Jun-14 supcvglem ---         deleted
11-Jun-14 reccnv    divcnv      revised
11-Jun-14 binom11i  binom11
11-Jun-14 binom1pi  binom1p     revised
11-Jun-14 binomi    binom       revised
11-Jun-14 ---       ---         binomlem1 - binomlem6 deleted
11-Jun-14 ser0cji   ---         deleted; see sercj
11-Jun-14 serzcji   sercj       revised
11-Jun-14 serzimi   serim       revised
11-Jun-14 serzrei   serre       revised
11-Jun-14 serzrelem ---         deleted
11-Jun-14 ser1mulci ---         deleted; see seqdistr
11-Jun-14 ser0mulci ---         deleted; see seqdistr
11-Jun-14 serzmulci ---         deleted; see seqdistr
11-Jun-14 serzmulc1 ---         deleted; see seqdistr
11-Jun-14 serzsplit ---         deleted; see seqsplit
11-Jun-14 serzcmp0  serge0      revised
11-Jun-14 serzcmp   sercmp      revised
11-Jun-14 serz0     ser0        revised
11-Jun-14 serz1p    seq1p       revised
11-Jun-14 serzrefi  serfre      revised
11-Jun-14 serzrecl  ---         deleted; see serfre
11-Jun-14 serzcl2   ---         deleted; see serf
11-Jun-14 ser1ser0i ---         deleted; see seq1p
11-Jun-14 ser1cl    ---         deleted; see seqcl
11-Jun-14 ser0cl    ---         deleted; see seqcl
11-Jun-14 serzcl    ---         deleted; see seqcl
11-Jun-14 fsumabs2mul ---       deleted; see fsum2mul and fsumabs
11-Jun-14 fsumabs   [--same--]  revised
11-Jun-14 fsum00    [--same--]  revised
11-Jun-14 fsumcmpndx2 fsumcmpss revised
11-Jun-14 fsumcmp0  fsumge0     revised
11-Jun-14 fsumcmp   [--same--]  revised
11-Jun-14 fsum0     ---         deleted; see sumz
11-Jun-14 fsumconst [--same--]  revised
11-Jun-14 fsum2mul  [--same--]  revised
11-Jun-14 fsumsub   [--same--]  revised
11-Jun-14 fsumneg   [--same--]  revised
11-Jun-14 fsumdivcALT ---       deleted
11-Jun-14 fsumdivc  [--same--]  revised
11-Jun-14 fsummulc2 fsummulc1   revised
11-Jun-14 fsummulc1 fsummulc2   revised
11-Jun-14 fsumshftm [--same--]  revised
11-Jun-14 fsumshft  [--same--]  revised
11-Jun-14 fsumrev2  [--same--]  revised
11-Jun-14 fsumrev   [--same--]  revised
11-Jun-14 fsumcom   [--same--]  revised
11-Jun-14 csbfsum   [--same--]  deleted; see sumeq2sdv
11-Jun-14 csbfsumlem [--same--] deleted
11-Jun-14 fsum4     [--same--]  deleted; see fsump1i
11-Jun-14 fsum3     [--same--]  deleted; see fsump1i
11-Jun-14 fsum2     [--same--]  deleted; see fsump1i
11-Jun-14 fsumadd   [--same--]  revised
11-Jun-14 fsumid2   ---         deleted; see fsumss
11-Jun-14 fsum0split ---        deleted; see fsumsplit
11-Jun-14 fsumsplit [--same--]  revised
11-Jun-14 fsum1p    [--same--]  revised
11-Jun-14 fsum1ps   ---         deleted; see fsum1p
11-Jun-14 fsumrecl  [--same--]  revised
11-Jun-14 fsum0cl   ---         deleted; see fsumcl
11-Jun-14 fsumcl    [--same--]  revised
11-Jun-14 fsumcllem [--same--]  revised; see this or fsumcl2lem
11-Jun-14 fsump1s   ---         deleted; see fsump1
11-Jun-14 fsump1slem ---        deleted
11-Jun-14 fsump1fi  ---         deleted; see fsump1
11-Jun-14 fsum1s2   ---         deleted; see sumsns
11-Jun-14 fsum1s    ---         deleted; see sumsns
11-Jun-14 fsum1slem ---         deleted
11-Jun-14 fsum1fi   ---         deleted; see fsum1
11-Jun-14 fsump1i   fsump1      revised
11-Jun-14 fsum1i    fsum1       revised
11-Jun-14 serzfsum  ---         deleted; see fsumser
11-Jun-14 fsumserz2 ---         deleted; see fsumser
11-Jun-14 fsumser1fi ---        deleted; see fsumser
11-Jun-14 fsumser0fi ---        deleted; see fsumser
11-Jun-14 fsumserzfi ---        deleted; see fsumser
11-Jun-14 fsumserz  fsumser     revised
11-Jun-14 dffsum    ---         deleted; see fsumser
11-Jun-14 sumeqfv   sumfc       revised
11-Jun-14 df-sum    [--same--]  revised
11-Jun-14 cvgcmp3ce cvgcmpce    revised
11-Jun-14 cvgcmp3cetlem2 ---    deleted
11-Jun-14 cvgcmp3cetlem1 ---    deleted
11-Jun-14 cvgcmp3cei ---        deleted; see cvgcmpce
11-Jun-14 cvgcmp3ci ---         deleted; see cvgcmpce
11-Jun-14 cvgcmpubi cvgcmpub    revised
11-Jun-14 cvgcmpi   cvgcmp      revised
11-Jun-14 cvgcmp2ci ---         deleted; see cvgcmp
11-Jun-14 cvgcmp2clemOLD ---    deleted
11-Jun-14 cvgcmp2clem ---       deleted
11-Jun-14 cvgcmp2i  ---         deleted; see cvgcmp
11-Jun-14 cvgcmp2lem ---        deleted
11-Jun-14 iserzabsi iserabs     revised
11-Jun-14 iserzabslem ---       deleted
11-Jun-14 ser1cmp2i ---         deleted
11-Jun-14 ser1cmp2lem ---       deleted
11-Jun-14 ser1cmp0i ---         deleted; see serge0
11-Jun-14 ser1cmpi  ---         deleted; see serle
11-Jun-14 ser1clim0 ---         deleted; see serclim0
11-Jun-14 ser10     ---         deleted; see ser0
11-Jun-14 ser1consti ser1const  revised
11-Jun-14 ser1f0i   ---         deleted; see serf0
11-Jun-14 serzf0i   serf0       revised
11-Jun-14 caucvg3   caucvg      revised
11-Jun-14 caucvg3i  ---         deleted; see caucvg
11-Jun-14 caucvg3lem ---        deleted
11-Jun-14 caucvg2i  caurcvg2    revised
11-Jun-14 caucvg3ai ---         deleted; see caucvg
11-Jun-14 caucvgi   caurcvg     revised
11-Jun-14 ---       ---         caucvglem1 - caucvglem6 deleted
11-Jun-14 climcaui  climcau     revised
11-Jun-14 climsupi  climsup     revised
11-Jun-14 climubi   ---         deleted; see monoord
11-Jun-14 climubii  ---         deleted; see monoord
11-Jun-14 climimi   climim      revised
11-Jun-14 climrei   climre      revised
11-Jun-14 climcji   climcj      revised
11-Jun-14 climabsi  climabs     revised
11-Jun-14 climabslem climcn1lem revised
11-Jun-14 climserzlei climserle revised
11-Jun-14 iserzexi  ---         deleted; see iserex
11-Jun-14 clim2serzi ---        deleted; see clim2ser
11-Jun-14 iserzshfti isershft   revised
11-Jun-14 iserzcmp0 iserge0     revised
11-Jun-14 iserzcmp  isercmp     revised
11-Jun-14 climsqueeze2 [--same--] revised
11-Jun-14 climsqueeze [--same--] revised
11-Jun-14 climcmpc1 climcmpc2   revised
11-Jun-14 climcmp   [--same--]  revised
11-Jun-14 climcmplem ---        deleted
11-Jun-14 iserzmulc1 isermulc2  revised
11-Jun-14 iserzex   iserex      revised
11-Jun-14 clim2serz clim2ser    revised
11-Jun-14 climmulci ---         deleted; see climmulc2
11-Jun-14 climaddci ---         deleted; see climaddc2
11-Jun-14 climsubc2 [--same--]  revised
11-Jun-14 climsub   [--same--]  revised
11-Jun-14 climmulc2 [--same--]  revised
11-Jun-14 climmul   [--same--]  revised
11-Jun-14 ---       ---         climmullem1 - climmullem8 deleted
11-Jun-14 climaddc2 [--same--]  revised
11-Jun-14 climaddc1 [--same--]  revised
11-Jun-14 climadd   [--same--]  revised
11-Jun-14 ---       ---         climaddlem1 - climaddlem3 deleted
11-Jun-14 climabs0i climabs0    revised
11-Jun-14 climge0   [--same--]  revised
11-Jun-14 climfnrcli ---        deleted; see climrecl
11-Jun-14 climrecl  [--same--]  revised
11-Jun-14 serzclim0 serclim0    revised
11-Jun-14 climuz0i  ---         deleted; see climconst2
11-Jun-14 iserzshft2i ---       deleted; see isershft
11-Jun-14 climshft2 [--same--]  revised
11-Jun-14 sershft   isershft
11-Jun-14 climshft  [--same--]  revised
11-Jun-14 climres   [--same--]  revised
11-Jun-14 2climnn0  ---         deleted; see 2clim
11-Jun-14 2climnn   ---         deleted; see 2clim
11-Jun-14 climeq    [--same--]  revised
11-Jun-14 climunii  ---         deleted; see climuni
11-Jun-14 clim0     climz
11-Jun-14 climconst3 ---        deleted; see climconst2
11-Jun-14 climconst2 [--same--] revised
11-Jun-14 climconsti climconst  revised
11-Jun-14 clmfnn    ---         deleted; see clim2c
11-Jun-14 climfnn   ---         deleted; see clim2c
11-Jun-14 clmi2a    ---         deleted; see climi2
11-Jun-14 clm4a     ---         deleted; see clim2c
11-Jun-14 clm0ii    ---         deleted; see climi0
11-Jun-14 clmi2rpi  ---         deleted; see climi2
11-Jun-14 clmi2i    ---         deleted; see climi2
11-Jun-14 clmi1i    ---         deleted; see climi
11-Jun-14 clm0nnsi  ---         deleted; see clim0c
11-Jun-14 clmnnsi   ---         deleted; see clim2c
11-Jun-14 clm0i     ---         deleted; see clim0c
11-Jun-14 clm4fi    ---         deleted; see clim2c
11-Jun-14 clm4lei   ---         deleted; see clim2c
11-Jun-14 clm3i     ---         deleted; see clim2c
11-Jun-14 clm2i     ---         deleted; see clim2
11-Jun-14 clm1i     ---         deleted; see clim2
11-Jun-14 climcl    [--same--]  changed variable names
11-Jun-14 clim      [--same--]  revised
11-Jun-14 ser1absdifi ---       deleted; see fsumabs or seqabs
11-Jun-14 ser1absdiflem ---     deleted
11-Jun-14 cauimi    ---         deleted
11-Jun-14 caurei    ---         deleted
11-Jun-14 caubndi   caubnd      revised
11-Jun-14 cvganuzi  rexanuz2    revised
11-Jun-14 cvganz    rexanuz     revised
11-Jun-14 cvg3i     ---         deleted; see rexuz3
11-Jun-14 cvg2i     ---         deleted
11-Jun-14 cvg1      ---         deleted
11-Jun-14 cvg1i     ---         deleted
11-Jun-14 cau5i     ---         deleted; see rexuz3
11-Jun-14 cau4ii    ---         deleted; see rexuz3
11-Jun-14 cau5ii    ---         deleted; see rexuz3
11-Jun-14 cau3i     cau3        revised
11-Jun-14 cau3iri   ---         deleted; see cau3
11-Jun-14 cau3ii    ---         deleted
11-Jun-14 cau2i     ---         deleted
11-Jun-14 seq1ubi   ---         deleted; see fimaxre3 and suprub
11-Jun-14 seq1ublem ---         deleted
11-Jun-14 seq1bndi  ---         deleted; see fimaxre3
11-Jun-14 sqsqr     resqrth
11-Jun-14 discrlem  discr       revised
11-Jun-14 ---       ---         discrlem1 - discrlem3 deleted
11-Jun-14 expnlbnd2 [--same--]  revised
11-Jun-14 expword2i [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expord2   [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expwordi  [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expord    [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expcan    [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expordi   [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expm1     [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expsubOLD ---         deleted; see expsub
11-Jun-14 expsub    [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 exprecOLD ---         deleted; see exprec
11-Jun-14 exprec    [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expgt0    [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expne0i   [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 1exp      [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 rpexpcl   [--same--]  generalized antecedent to N e. ZZ
11-Jun-14 expval    [--same--]  revised
11-Jun-14 df-exp    [--same--]  revised
11-Jun-14 ser0p1i   ---         deleted; see seqp1i
11-Jun-14 ser00i    ---         deleted; see seq1i
11-Jun-14 ser0fi    ---         deleted; see serf
11-Jun-14 ser0cl1i  ---         deleted; see serf
11-Jun-14 serzcl1i  ---         deleted; see serf
11-Jun-14 seq1resval2g ---      deleted; see seqfveq
11-Jun-14 seqzresval2g ---      deleted; see seqfveq
11-Jun-14 seq1alcl  ---         deleted; see seqcl
11-Jun-14 seqzalcl  ---         deleted; see seqcl
11-Jun-14 seq0cl    ---         deleted; see seqf
11-Jun-14 seqzres2  ---         deleted; see seqres
11-Jun-14 seqzres   ---         deleted; see seqres
11-Jun-14 seqzresval ---        deleted; see seqfveq
11-Jun-14 seqzcl    ---         deleted; see seqf
11-Jun-14 seqzrn    ---         deleted; see seqf
11-Jun-14 seqzrn2   ---         deleted; see seqf2
11-Jun-14 seqzfveqg ---         deleted; see seqfveq
11-Jun-14 seqzeq    ---         deleted; see seqfeq
11-Jun-14 seqzfveq  ---         deleted; see seqfveq
11-Jun-14 seq1seqzg ---         deleted
11-Jun-14 seqzp1g   ---         deleted; see seqp1
11-Jun-14 seqz1g    ---         deleted; see seq1
11-Jun-14 seq01     ---         deleted; see seqp1i
11-Jun-14 seqzm1    ---         deleted; see seqm1
11-Jun-14 seq1shftid ---        deleted; see seqfeq
11-Jun-14 ser1addi  ---         deleted; see seradd
11-Jun-14 ser1add2i ---         deleted; see seradd
11-Jun-14 ser1monoi ---         deleted; see sermono
11-Jun-14 ser1p1i   ---         deleted; see seqp1i
11-Jun-14 ser11i    ---         deleted; see seq1i
11-Jun-14 ser1f2i   ---         deleted; see serf
11-Jun-14 ser1cl2i  ---         deleted; see serf
11-Jun-14 ser1refi  ---         deleted; see serfre
11-Jun-14 ser1recli ---         deleted; see serfre
11-Jun-14 ser1cl1i  ---         deleted; see serf
11-Jun-14 ser1fi    ---         deleted; see serf
11-Jun-14 ser1f     ---         deleted; see serf
11-Jun-14 seq1p1g   ---         deleted; see seqp1
11-Jun-14 seq11g    ---         deleted; see seq1
11-Jun-14 seq1res   ---         deleted; see seqres
11-Jun-14 seq1cl2   ---         deleted; see seqcl2
11-Jun-14 seq1cl    ---         deleted; see seqcl
11-Jun-14 seq1f2    ---         deleted; see seqf2
11-Jun-14 seq1f     ---         deleted; see seqf
11-Jun-14 seq1rn    ---         deleted; see seqf
11-Jun-14 seq1rn2   ---         deleted; see seqf2
11-Jun-14 seq1m1    ---         deleted; see seqm1
11-Jun-14 seq1lem2  ---         deleted
11-Jun-14 seq0p1    ---         deleted; see seqp1
11-Jun-14 seq00     ---         deleted; see seq1
11-Jun-14 seqzp1    ---         deleted; see seqp1
11-Jun-14 seqz1     ---         deleted; see seq1
11-Jun-14 seq0fn    ---         deleted; see seqfn
11-Jun-14 seq0seqz  ---         deleted
11-Jun-14 seq1seqz  ---         deleted
11-Jun-14 seqzfn    ---         deleted; see seqfn
11-Jun-14 seqzfval  ---         deleted
11-Jun-14 seq0fval  ---         deleted
11-Jun-14 seq1fn    ---         deleted; see seqfn
11-Jun-14 seq1p1    ---         deleted; see seqp1
11-Jun-14 seq11     ---         deleted; see seq1
11-Jun-14 seq1fval  ---         deleted
11-Jun-14 df-seqz   ---         deleted; see df-seq
11-Jun-14 df-seq0   ---         deleted; see df-seq
11-Jun-14 df-seq1   ---         deleted; see df-seq
11-Jun-14 cseqz     ---         deleted                - use seq theorems
11-Jun-14 cseq0     ---         deleted                  in place of seq1, etc.
11-Jun-14 cseq1     ---         deleted
11-Jun-14 sercmp    [--same--]  revised
11-Jun-14 ser0      [--same--]  revised
11-Jun-14 serdistr  [--same--]  revised
11-Jun-14 seqhomo   [--same--]  revised
11-Jun-14 seqid2    [--same--]  revised
11-Jun-14 seqid     [--same--]  revised
11-Jun-14 sersub    [--same--]  revised
11-Jun-14 seradd    [--same--]  revised
11-Jun-14 serf1o    [--same--]  revised
11-Jun-14 serf1olem2 [--same--] revised
11-Jun-14 serf1olem1 [--same--] revised
11-Jun-14 sercaopr  [--same--]  revised
11-Jun-14 seq1p     [--same--]  revised
11-Jun-14 seqsplit  [--same--]  revised
11-Jun-14 sermono   [--same--]  revised
11-Jun-14 monoord   [--same--]  revised
11-Jun-14 serfre    [--same--]  revised
11-Jun-14 serf      [--same--]  revised
11-Jun-14 seqres    [--same--]  revised
11-Jun-14 seqshft2  [--same--]  revised
11-Jun-14 seqfeq    [--same--]  revised
11-Jun-14 seqfveq   [--same--]  revised
11-Jun-14 seqfeq2   [--same--]  revised
11-Jun-14 seqfveq2  [--same--]  revised
11-Jun-14 seqf      [--same--]  revised
11-Jun-14 seqcl     [--same--]  revised
11-Jun-14 seqf2     [--same--]  revised
11-Jun-14 seqcl2    [--same--]  revised
11-Jun-14 caoprassg [--same--]  revised
11-Jun-14 caoprcomg [--same--]  revised
11-Jun-14 fvunsn    [--same--]  eliminate unnecessary hypothesis
29-May-14 iccss2    [--same--]  moved from JM's mathbox to main set.mm
29-May-14 iccss     [--same--]  moved from JM's mathbox to main set.mm
29-May-14 iccconn   [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 retopcon  [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 reconn    [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 reconnlem5 [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 reconnlem4 [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 reconnlem3 [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 reconnlem2 [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 reconnlem1 [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 connsub   [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 dfcon2    [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 ioodisj   [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 ccid      [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 imp511    [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 imp55     [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 imp5g     [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 mtord     [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 eqeu      [--same--]  moved from JGH's mathbox to main set.mm
29-May-14 uznnssnn  [--same--]  moved from SF's mathbox to main set.mm
22-May-14 dmnrng    dmnrngo     (in FL's mathbox)
22-May-14 smprngpr  smprngopr   (in FL's mathbox)
22-May-14 prrngrng  prrngorngo  (in FL's mathbox)
22-May-14 isprrng   isprrngo    (in FL's mathbox)
22-May-14 df-prrng  df-prrngo   (in FL's mathbox)
22-May-14 0ring     0rngo       (in FL's mathbox)
22-May-14 rngidl    rngoidl     (in FL's mathbox)
22-May-14 crnghomfo crngohomfo  (in FL's mathbox)
22-May-14 crngrng   crngorngo   (in FL's mathbox)
22-May-14 iscring2  iscrngo2    (in FL's mathbox)
22-May-14 iscring   iscrngo     (in FL's mathbox)
22-May-14 df-cring  df-crngo    (in FL's mathbox)
22-May-14 rngisoco  rngoisoco   (in FL's mathbox)
22-May-14 rngisocnv rngoisocnv  (in FL's mathbox)
22-May-14 rngisohom rngoisohom  (in FL's mathbox)
22-May-14 rngiso1o  rngoiso1o   (in FL's mathbox)
22-May-14 isrngiso  isrngoiso   (in FL's mathbox)
22-May-14 rngisoval rngoisoval  (in FL's mathbox)
22-May-14 df-rngiso df-rngoiso  (in FL's mathbox)
22-May-14 rngkerinj rngokerinj  (in FL's mathbox)
22-May-14 rnghomco  rngohomco   (in FL's mathbox)
22-May-14 rnghomsub rngohomsub  (in FL's mathbox)
22-May-14 rnghom0   rngohom0    (in FL's mathbox)
22-May-14 rnggrphom rngogrphom  (in FL's mathbox)
22-May-14 rnghommul rngohommul  (in FL's mathbox)
22-May-14 rnghomadd rngohomadd  (in FL's mathbox)
22-May-14 rnghom1   rngohom1    (in FL's mathbox)
22-May-14 rnghomcl  rngohomcl   (in FL's mathbox)
22-May-14 rnghomf   rngohomf    (in FL's mathbox)
22-May-14 isrnghom  isrngohom   (in FL's mathbox)
22-May-14 rnghomval rngohomval  (in FL's mathbox)
22-May-14 df-rnghom df-rngohom  (in FL's mathbox)
22-May-14 isdivrng3 isdrngo3    (in FL's mathbox)
22-May-14 isdivrng2 isdrngo2    (in FL's mathbox)
22-May-14 isdivrng1 isdrngo1    (in FL's mathbox)
22-May-14 ringsubdir rngosubdir (in FL's mathbox)
22-May-14 ringsubdi rngosubdi   (in FL's mathbox)
22-May-14 ringnegrmul rngonegrmul (in FL's mathbox)
22-May-14 ringneglmul rngoneglmul (in FL's mathbox)
22-May-14 ringnegmn1r rngonegmn1r (in FL's mathbox)
22-May-14 ringnegmn1l rngonegmn1l (in FL's mathbox)
22-May-14 ringsub   rngosub     (in FL's mathbox)
22-May-14 ringaddneg2 rngoaddneg2 (in FL's mathbox)
22-May-14 ringaddneg1 rngoaddneg1 (in FL's mathbox)
22-May-14 ringnegcl rngonegcl   (in FL's mathbox)
22-May-14 df-toprng df-toprngo  (in FL's mathbox)
22-May-14 glmring   glmrngo     (in FL's mathbox)
22-May-14 rngridfz  rngoridfz   (in FL's mathbox)
22-May-14 rngunval2 rngounval2  (in FL's mathbox)
22-May-14 rnginvcl  rngoinvcl   (in FL's mathbox)
22-May-14 rnplrnml3 rngodmeqrn  (in FL's mathbox)
22-May-14 rngdmdmrn rngodmdmrn  (in FL's mathbox)
22-May-14 uznzr     rngoueqz
22-May-14 ring1cl   rngo1cl
22-May-14 on1el6    rngosn6
22-May-14 on1el4    rngosn4
22-May-14 on1el3    rngosn3
22-May-14 ringoridm rngoridm
22-May-14 ringolidm rngolidm
22-May-14 ringoidmlem rngoidmlem
22-May-14 fora      rngoablo2
22-May-14 fora2     rngoablo2lem2
22-May-14 fora1     rngoablo2lem1
22-May-14 unmnd     rngomnd
22-May-14 rnplrnml  rngorn1eq
22-May-14 rnplrnml2 rngorn1
22-May-14 rnplrnml0 rngodm1dm2
22-May-14 rngn0     rngon0
22-May-14 drngi     drngoi
22-May-14 ringsn    rngosn
22-May-14 cnring    cnrngo
22-May-14 ringorz   rngorz
22-May-14 ringolz   rngolz
22-May-14 ring0lid  rngo0lid
22-May-14 ring0rid  rngo0rid
22-May-14 ring0cl   rngo0cl
22-May-14 ringlcan  rngolcan
22-May-14 ringrcan  rngorcan
22-May-14 ringa4    rngoa4
22-May-14 ringa32   rngoa32
22-May-14 ringaass  rngoaass
22-May-14 ringcom   rngocom
22-May-14 ringgcl   rngogcl
22-May-14 ringogrpo rngogrpo
22-May-14 ringoablo rngoablo
22-May-14 ring2     rngo2
22-May-14 ringoass  rngoass
22-May-14 ringodir  rngodir
22-May-14 ringodi   rngodi
22-May-14 ringoideu rngoideu
22-May-14 ringid    rngoid
22-May-14 ringocl   rngocl
22-May-14 ringsm    rngosm
22-May-14 ringoi    rngoi
22-May-14 isringod  isrngod
22-May-14 isringo   isrngo
22-May-14 relrng    relrngo
22-May-14 df-ringo  df-rngo
22-May-14 cring     crngo
21-May-14 infmrgelb [--same--]  moved from JM's mathbox to main set.mm; revised
21-May-14 infmrlb   [--same--]  moved from JM's mathbox to main set.mm; revised
21-May-14 fienf1f1o ---         deleted; use f1finf1o
21-May-14 lbleinf   infmrgelb   moved from JGH's mathbox to main set.mm
21-May-14 divcan7   [--same--]  moved from JGH's mathbox to main set.mm
21-May-14 blhalf    [--same--]  moved from JM's mathbox to main set.mm
21-May-14 lt0nnn0   [--same--]  revised
17-May-14 oprabval2ga ---       deleted; use ovmpt2g
17-May-14 mpt2fng   ---         deleted; use fnmpt2
17-May-14 rngop     rnmpt2
17-May-14 fnoprab2ga fnmpt2
17-May-14 fnoprab2a fnmpt2i
17-May-14 dmoprab2a dmmpt2
17-May-14 foprab2a  fmpt2
17-May-14 oprabex2ga mpt2exg
17-May-14 mpt2exg   mpt2exga
17-May-14 dmmpt2    dmmpt
17-May-14 dmmpt     dmmptg
17-May-14 visset    vex
17-May-14 elisseti  elexi
17-May-14 elissetxx elisset
17-May-14 elisset   elex
17-May-14 elex      elissetxx
17-May-14 syl111anc syl3anc
17-May-14 syl11anc  syl2anc
11-Mar-14 syl2anc   syl2anr
 7-May-14 peano5uztiOLD ---     deleted
 7-May-14 peano5uziOLD ---      deleted
 7-May-14 dfnn2     dfnn3
 7-May-14 dfnn3     ---         deleted from JH's mathbox; see df-n
19-Apr-14 mod0      [--same--]  moved from JM's mathbox to main set.mm
19-Apr-14 invrcl    ---         deleted; use drnginvrcl and drnginvn0
16-Apr-14 grpkerinj grpokerinj  (in JM's mathbox)
16-Apr-14 grpeqdivid grpoeqdivid (in JM's mathbox)
16-Apr-14 grphm     grpohm      (in FL's mathbox)
16-Apr-14 grphlem5  grpohlem5   (in FL's mathbox)
16-Apr-14 grphmlem4 grpohmlem4  (in FL's mathbox)
16-Apr-14 grphlem3  grpohlem3   (in FL's mathbox)
16-Apr-14 grphmlem2 grpohmlem2  (in FL's mathbox)
16-Apr-14 grphmlem1 grpohmlem1  (in FL's mathbox)
16-Apr-14 grpdivzer grpodivzer  (in FL's mathbox)
16-Apr-14 grpdlcan  grpodlcan   (in FL's mathbox)
16-Apr-14 grpdrcan  grpodrcan   (in FL's mathbox)
16-Apr-14 grpdivfo  grpodivfo   (in FL's mathbox)
16-Apr-14 grpdivone grpodivone  (in FL's mathbox)
16-Apr-14 grpmnd    grpomnd     (in FL's mathbox)
16-Apr-14 grplactf1o grpolactf1o
16-Apr-14 grpnpncan grponpncan
16-Apr-14 grpnnncan2 grponnncan2
16-Apr-14 grppnpcan2 grpopnpcan2
16-Apr-14 grpnpcan  grponpcan
16-Apr-14 grppncan  grpopncan
16-Apr-14 grpdivid  grpodivid
16-Apr-14 grpmuldivass grpomuldivass
16-Apr-14 grpdivdiv grpodivdiv
16-Apr-14 grpdivcl  grpodivcl
16-Apr-14 grpdivf   grpodivf
16-Apr-14 grpdivval grpodivval
16-Apr-14 grpdivfval grpodivfval
16-Apr-14 grpinvdiv grpoinvdiv
16-Apr-14 grpdivinv grpodivinv
16-Apr-14 grpinvop  grpoinvop
16-Apr-14 grpinvf   grpoinvf
16-Apr-14 grp2inv   grpo2inv
16-Apr-14 grpasscan2 grpoasscan2
16-Apr-14 grpasscan1 grpoasscan1
16-Apr-14 grpsn     grposn
16-Apr-14 grprn     grporn
16-Apr-14 grprndm   grporndm
16-Apr-14 grpfo     grpofo
16-Apr-14 grp2grp   grpo2grp
 2-Apr-14 ---       ---         math token "Cgr" changed to "=="
 2-Apr-14 ---       ---         math token "(++)" changed to "(+)"
 2-Apr-14 ---       ---         math token "(+)" changed to "\/_"
31-Mar-14 grpinvcl  [--same--]  removed redundant hypothesis
31-Mar-14 ---       ---         math token "-g" changed to "invg"
23-Mar-14 hbequid2  ---         deleted; use hbequid
22-Mar-14 firnfi4   ---         deleted from JM's mathbox; see abrexfi
22-Mar-14 firnfi3   ---         deleted from JM's mathbox; see abrexfi
22-Mar-14 firnfi2   ---         deleted from JM's mathbox; see abrexfi
22-Mar-14 firnfi    ---         deleted from JM's mathbox; see abrexfi
22-Mar-14 cvol      clvol
22-Mar-14 fimaxre2  [--same--]  moved from JM's mathbox to main set.mm; revised
22-Mar-14 fimaxre   [--same--]  moved from JM's mathbox to main set.mm
15-Mar-14 reef11i   ---         deleted; see reef11
15-Mar-14 fsumsub   [--same--]  moved from SF's mathbox to main set.mm
15-Mar-14 fsumneg   [--same--]  moved from SF's mathbox to main set.mm
15-Mar-14 bccmpl    [--same--]  revised
15-Mar-14 ---       ---         fseq1p1m1lem1 - fseq1p1m1lem3 deleted
15-Mar-14 fz1eqblem ---         deleted
15-Mar-14 fzsuc     [--same--]  revised; see also fzsuc2
15-Mar-14 uz2m1nn   [--same--]  moved from PC's mathbox to main set.mm
15-Mar-14 elnn00nn  ---         deleted; see elnn0
15-Mar-14 npncan3   [--same--]  moved from SF's mathbox to main set.mm
15-Mar-14 npncan2   [--same--]  moved from SF's mathbox to main set.mm
12-Mar-14 copsexgb  coprsexg
 9-Mar-14 grpid     [--same--]  revised
 2-Mar-14 bnj1150   unssd       moved from JBN's mathbox to main set.mm
28-Feb-14 f1oeq23   [--same--]  moved from FL's mathbox to main set.mm
28-Feb-14 fzp1elp1  [--same--]  moved from JM's mathbox to main set.mm
28-Feb-14 divides2  [--same--]  moved from JGH's mathbox to main set.mm
28-Feb-14 fzfi2     ---         deleted from JM's mathbox; see fzfi
28-Feb-14 fzfi      [--same--]  moved from JM's mathbox; revised
28-Feb-14 fz1fi     ---         deleted; see fzfi
25-Feb-14 biadan2   [--same--]  moved from JM's mathbox to main set.mm
23-Feb-14 op1steq   [--same--]  generalized antecedent from _V X. _V to V X. W
23-Feb-14 eqop      [--same--]  generalized antecedent from _V X. _V to V X. W
23-Feb-14 eqopi     [--same--]  generalized antecedent from _V X. _V to V X. W
20-Feb-14 eqreldv2  [--same--]  moved from RM's mathbox to main set.mm; revised
20-Feb-14 eqreldv   [--same--]  moved from RM's mathbox to main set.mm
17-Feb-14 qnnenOLD  ---         deleted; see qnnen
17-Feb-14 divvali   divval      revised
17-Feb-14 receui    receu       revised
17-Feb-14 recexi    ---         deleted; see recex
17-Feb-14 ax-cnex   ---         deleted; see cnex
17-Feb-14 axcnex    ---         deleted; see cnex
17-Feb-14 srex      ---         deleted
 4-Feb-14 abl23     ablo32
 4-Feb-14 abl4      ablo4
 4-Feb-14 abldiv23  ablodiv32
 4-Feb-14 nvadd23   nvadd32
 4-Feb-14 vca23     vca32
 4-Feb-14 ringa23   ringa32
 4-Feb-14 divdiv23i divdiv32i
 4-Feb-14 divdiv23  divdiv32
 4-Feb-14 sub23     sub32
 4-Feb-14 dif23     dif32
 4-Feb-14 or23      or32
30-Jan-14 heibor    [--same--]  revised
30-Jan-14 ---       ---         heiborlem11 - heiborlem42 deleted
30-Jan-14 heiborlem10 [--same--] revised
30-Jan-14 heiborlem9 [--same--] revised
30-Jan-14 heiborlem8 [--same--] revised
30-Jan-14 heiborlem7 [--same--] revised
30-Jan-14 heiborlem6 [--same--] revised
30-Jan-14 heiborlem5 [--same--] revised
30-Jan-14 heiborlem4 [--same--] revised
30-Jan-14 heiborlem3 [--same--] revised
30-Jan-14 heiborlem2 [--same--] revised
30-Jan-14 heiborlem1 [--same--] revised
30-Jan-14 ismtyhmeolem [--same--] revised
30-Jan-14 hmopbdopiHIL ---      deleted; see hmopbdoptHIL
30-Jan-14 htthi     htth        revised
30-Jan-14 ---       ---         htthlem1 - htthlem12 deleted
30-Jan-14 ubthi     ubth        revised
30-Jan-14 ubthii    ---         deleted; see ubth
30-Jan-14 ---       ---         ubthlem4 - ubthlem14 deleted
30-Jan-14 ubthlem3  [--same--]  revised
30-Jan-14 ubthlem2  [--same--]  revised
30-Jan-14 ubthlem1  [--same--]  revised
30-Jan-14 bcth      [--same--]  revised
30-Jan-14 ---       ---         bcthlem6 - bcthlem33 deleted
30-Jan-14 bcthlem5  [--same--]  revised
30-Jan-14 bcthlem4  [--same--]  revised
30-Jan-14 bcthlem3  [--same--]  revised
30-Jan-14 bcthlem2  [--same--]  revised
30-Jan-14 bcthlem1  [--same--]  revised
30-Jan-14 fimax     ---         deleted; see fimaxg
30-Jan-14 ac6sfilem3 ---        deleted
30-Jan-14 ac6sfilem2 ---        deleted
30-Jan-14 ac6sfilem1 ---        deleted
30-Jan-14 metdcn    [--same--]  revised
30-Jan-14 ---       ---         metnrmlem4 - metnrmlem6 deleted
30-Jan-14 metnrmlem3 [--same--] revised
30-Jan-14 metnrmlem2 [--same--] revised
30-Jan-14 metnrmlem1 [--same--] revised
30-Jan-14 altretoplem2 ---      deleted
30-Jan-14 altretoplem1 ---      deleted
30-Jan-14 bsi3      bsi
30-Jan-14 bsi2      ---         deleted; see bsi
30-Jan-14 bsi       [--same--]  revised
30-Jan-14 subtopmetlem ---      deleted
30-Jan-14 basmetres ---         deleted; see metssba2
30-Jan-14 nvcnpi4   ---         deleted; see metcnpi4
30-Jan-14 nvcnpi3   ---         deleted; see metcnpi3
30-Jan-14 nmcn3     ---         deleted; see nmcn
30-Jan-14 nmcn2     ---         deleted; see nmcn
30-Jan-14 nmcni     ---         deleted; see nmcn
30-Jan-14 nmcnilem  ---         deleted
30-Jan-14 sqcn2     ---         deleted; see sqcn
30-Jan-14 sqcn      [--same--]  revised
30-Jan-14 nvcni3    ---         deleted; see metcni
30-Jan-14 nvcni2    ---         deleted; see metcni
30-Jan-14 nvcni     ---         deleted; see metcni
30-Jan-14 nvcnpf    ---         deleted; see metcnpf
30-Jan-14 nvcnf     ---         deleted; see metcnf
30-Jan-14 nvelbl2   [--same--]  revised
30-Jan-14 nvelbl    [--same--]  revised
30-Jan-14 metcnp4OLD ---        deleted
30-Jan-14 metcnp4lem2 [--same--] revised
30-Jan-14 metelclsOLD ---       deleted
30-Jan-14 tgioolem  ---         deleted
30-Jan-14 bl2ioo    [--same--]  revised
30-Jan-14 metcnp3   [--same--]  revised
30-Jan-14 metcni2   [--same--]  revised
30-Jan-14 metcni    [--same--]  revised
30-Jan-14 metcnpi4  [--same--]  revised
30-Jan-14 metcnpi3  [--same--]  revised
30-Jan-14 metcnpi2  [--same--]  revised
30-Jan-14 metcnpi   [--same--]  revised
30-Jan-14 metcn     [--same--]  revised
30-Jan-14 metcnp2   [--same--]  revised
30-Jan-14 metcnp    [--same--]  revised
30-Jan-14 metcnplem [--same--]  revised
30-Jan-14 metequiv  [--same--]  revised
30-Jan-14 lpbl      [--same--]  revised
30-Jan-14 blnei     [--same--]  revised
30-Jan-14 metnei    [--same--]  revised
30-Jan-14 neibl     [--same--]  revised
30-Jan-14 blopn     [--same--]  revised
30-Jan-14 tgbl      ---         deleted; see opnval
30-Jan-14 opni3     [--same--]  revised
30-Jan-14 opni2     [--same--]  revised
30-Jan-14 isopn4    [--same--]  revised
30-Jan-14 uniopn2   [--same--]  revised
30-Jan-14 opnfval   ---         deleted
30-Jan-14 ssblex    [--same--]  revised
30-Jan-14 ssbl      [--same--]  revised
30-Jan-14 blssex    [--same--]  revised
30-Jan-14 blss      [--same--]  revised
30-Jan-14 blin      [--same--]  revised
30-Jan-14 rnblssm   ---         deleted; see blssm
30-Jan-14 blssm     [--same--]  revised
30-Jan-14 blex      ---         deleted; see unirnbl
30-Jan-14 blelrn    [--same--]  revised
30-Jan-14 blrn3     ---         deleted; see blrn
30-Jan-14 bln0      [--same--]  revised
30-Jan-14 blcntr    [--same--]  revised
30-Jan-14 blf       [--same--]  revised
30-Jan-14 bl2in     [--same--]  revised
30-Jan-14 blrn2     ---         deleted; see blrn
30-Jan-14 blrn      [--same--]  revised
30-Jan-14 elbl3     [--same--]  revised
30-Jan-14 elbl2     [--same--]  revised
30-Jan-14 elbl      [--same--]  revised
30-Jan-14 blval     [--same--]  revised
30-Jan-14 metdmdm   ---         deleted; see a1i
30-Jan-14 df-opn    [--same--]  revised
30-Jan-14 uniretop  [--same--]  revised
30-Jan-14 unirnioo  [--same--]  revised
30-Jan-14 qjust     ---         deleted
30-Jan-14 df-q      [--same--]  revised
30-Jan-14 unifo     iunfo       revised
30-Jan-14 oprelimab [--same--]  revised
30-Jan-14 oprvelrn  [--same--]  revised
16-Jan-14 resex     [--same--]  moved from JM's mathbox to main set.mm
16-Jan-14 ifeq2da   [--same--]  moved from JM's mathbox to main set.mm
16-Jan-14 ifeq1da   [--same--]  moved from JM's mathbox to main set.mm
16-Jan-14 fvif      [--same--]  moved from JM's mathbox to main set.mm
15-Jan-14 ifclda    [--same--]  moved from JM's mathbox to main set.mm
14-Jan-14 wl-adnestantdALT embantd moved from WL's mathbox to main set.mm
14-Jan-14 rabbirdv  rabbi2dva   revised hypothesis
13-Jan-14 19.23aexi exlimexi    (in AS's mathbox)
13-Jan-14 r19.23aib rexlimib    (in FL's mathbox)
13-Jan-14 r19.23advv rexlimdvv
13-Jan-14 r19.23aivv rexlimivv
13-Jan-14 r19.23adva rexlimdva
13-Jan-14 r19.23adv rexlimdv
13-Jan-14 r19.23ad2 rexlimd2
13-Jan-14 r19.23ad  rexlimd
13-Jan-14 r19.23aivw rexlimivw
13-Jan-14 r19.23aiva rexlimiva
13-Jan-14 r19.23aiv rexlimiv
13-Jan-14 r19.23ai  rexlimi
13-Jan-14 19.23advv exlimdvv
13-Jan-14 19.23aivv exlimivv
13-Jan-14 19.23aiv  exlimiv
13-Jan-14 19.23adv  exlimdv
13-Jan-14 19.23ad   exlimd
13-Jan-14 19.23ai   exlimi
13-Jan-14 19.21a3con13v alrim3con13v (In AS's mathbox)
13-Jan-14 r19.21advva ralrimdvva
13-Jan-14 r19.21advv ralrimdvv
13-Jan-14 r19.21aivva ralrimivva
13-Jan-14 r19.21aivv ralrimivv
13-Jan-14 r19.21adva ralrimdva
13-Jan-14 r19.21adv ralrimdv
13-Jan-14 r19.21ad  ralrimd
13-Jan-14 r19.21aiva ralrimiva
13-Jan-14 r19.21aiv ralrimiv
13-Jan-14 r19.21ai  ralrimi
13-Jan-14 19.21adv  alrimdv
13-Jan-14 19.21aivv alrimivv
13-Jan-14 19.21aiv  alrimiv
13-Jan-14 19.21ad   alrimd
13-Jan-14 19.21ai   alrimi
 9-Jan-14 dvrngprop drngprop
 9-Jan-14 dvrngid2  drngid2
 9-Jan-14 divrngunz drngunz
 9-Jan-14 divrngid  drngid
 9-Jan-14 divrngidlem drngidlem
 9-Jan-14 divrngmcl drngmcl
 9-Jan-14 divrngmgrp drngmgrp
 9-Jan-14 isdivrngrd isdrngrd
 9-Jan-14 isdivrngd isdrngd
 9-Jan-14 divrnggrp drnggrp
 9-Jan-14 divrngring drngrng
 9-Jan-14 isdivrng  isdrng
 9-Jan-14 cdivring  cdr
 9-Jan-14 ringrz    rngrz
 9-Jan-14 ringlz    rnglz
 9-Jan-14 isringd   isrngd
 9-Jan-14 isringid  isrngid
 9-Jan-14 ringridm  rngridm
 9-Jan-14 ringlidm  rnglidm
 9-Jan-14 ringidmlem rngidmlem
 9-Jan-14 ringgrp   rnggrp
 9-Jan-14 ringabl   rngabl
 9-Jan-14 ringidcl  rngidcl
 9-Jan-14 ringdir   rngdir
 9-Jan-14 ringdi    rngdi
 9-Jan-14 ringideu  rngideu
 9-Jan-14 ringass   rngass
 9-Jan-14 ringcl    rngcl
 9-Jan-14 ringi     rngi
 9-Jan-14 isring    isrng
 9-Jan-14 ringidval rngidval
23-Dec-13 cvimarndm cnvimarndm
23-Dec-13 cnvresima [--same--]  moved from JGH's mathbox to main set.mm
23-Dec-13 hstel     ishst
23-Dec-13 stel      isst        revised
23-Dec-13 df-hst    [--same--]  revised
23-Dec-13 df-st     [--same--]  revised
23-Dec-13 shsumval3i shsval3i
23-Dec-13 shsumval2i shsval2i
23-Dec-13 dfchj3    sshjval3    revised
23-Dec-13 dfchj2    sshjval2    revised
23-Dec-13 dfchsup2  ---         deleted; see hsupval2
23-Dec-13 shsumval  shsval      revised
23-Dec-13 df-chsup  [--same--]  revised
23-Dec-13 df-chj    [--same--]  revised
23-Dec-13 df-span   [--same--]  revised
23-Dec-13 df-shsum  df-shs      revised
23-Dec-13 dfch2     [--same--]  revised
23-Dec-13 ch2       isch3
23-Dec-13 chcmhi    ---         deleted; see isch3
23-Dec-13 chsscmi   ---         deleted; see isch3
23-Dec-13 closedsub isch2
23-Dec-13 df-ch     [--same--]  revised
23-Dec-13 sh2       issh3
23-Dec-13 sh        issh2
23-Dec-13 df-sh     [--same--]  revised
23-Dec-13 pjmval    pjfval      revised
23-Dec-13 df-pj     [--same--]  revised
23-Dec-13 df-oc     [--same--]  revised
23-Dec-13 dfhnorm2  [--same--]  revised
23-Dec-13 df-hvsub  [--same--]  revised
23-Dec-13 df-hnorm  [--same--]  revised
23-Dec-13 nvmfval   [--same--]  revised
23-Dec-13 iscringd  [--same--]  (in JM's mathbox) revised
23-Dec-13 flddivrng [--same--]  moved from JM's mathbox to main set.mm; revised
23-Dec-13 isringod  [--same--]  moved from JM's mathbox to main set.mm; revised
23-Dec-13 exidreslem [--same--] (in JM's mathbox) revised
23-Dec-13 extopgrp  [--same--]  (in FL's mathbox) revised
23-Dec-13 invtrgrp  ginvsn      moved from FL's mathbox to main set.mm; revised
23-Dec-13 idtrgrp   gidsn       moved from FL's mathbox to main set.mm; revised
23-Dec-13 zrfld     [--same--]  (in FL's mathbox) revised
23-Dec-13 fldi      [--same--]  (in FL's mathbox) revised
23-Dec-13 rngunval2 [--same--]  (in FL's mathbox) revised
23-Dec-13 ununr     [--same--]  (in FL's mathbox) revised
23-Dec-13 mndid     [--same--]  (in FL's mathbox) (in FL's mathbox) revised
23-Dec-13 zrdivrng  [--same--]  revised
23-Dec-13 rngmgmbs4 [--same--]  revised
23-Dec-13 ismnd2    [--same--]  revised
23-Dec-13 ismnd1    [--same--]  revised
23-Dec-13 ismnd     [--same--]  revised
23-Dec-13 isexid2   [--same--]  revised
23-Dec-13 isexid    [--same--]  revised
23-Dec-13 df-exid   [--same--]  revised
23-Dec-13 0vfval    [--same--]  revised
23-Dec-13 ringoideu [--same--]  revised
23-Dec-13 ringid    [--same--]  revised
23-Dec-13 ringoi    [--same--]  revised
23-Dec-13 isringo   [--same--]  revised
23-Dec-13 df-ringo  [--same--]  revised
23-Dec-13 gxnval    [--same--]  revised
23-Dec-13 gxpval    [--same--]  revised
23-Dec-13 gxval     [--same--]  revised
23-Dec-13 gxoprval  gxfval      revised
23-Dec-13 grpdivfval [--same--] revised
23-Dec-13 grpoinvval [--same--] revised
23-Dec-13 grpoinvfval [--same--] revised
23-Dec-13 grpoidval [--same--]  revised
23-Dec-13 grpidvallem ---       deleted
23-Dec-13 fungid    fngid       revised
23-Dec-13 gid0      ---         deleted
23-Dec-13 grprlidrid ---        deleted
23-Dec-13 df-gx     [--same--]  revised
23-Dec-13 df-gdiv   [--same--]  revised
23-Dec-13 df-ginv   [--same--]  revised
23-Dec-13 df-gid    [--same--]  revised
22-Dec-13 df-igen   [--same--]  (in JM's mathbox) revised
22-Dec-13 pcoval    [--same--]  (in JM's mathbox) revised
22-Dec-13 pcofval   [--same--]  (in JM's mathbox) revised
22-Dec-13 df-pi1    [--same--]  (in JM's mathbox) revised
22-Dec-13 df-pi1b   [--same--]  (in JM's mathbox) revised
22-Dec-13 df-pco    [--same--]  (in JM's mathbox) revised
22-Dec-13 txsubsp   [--same--]  (in JM's mathbox) revised
22-Dec-13 subspabs  ---         (in JM's mathbox) deleted; use subspco
22-Dec-13 subspopn  [--same--]  (in JM's mathbox) revised
22-Dec-13 fzm1      [--same--]  moved from JM's mathbox to main set.mm
22-Dec-13 elfzp12   [--same--]  moved from JM's mathbox to main set.mm
22-Dec-13 zornn0    [--same--]  moved from JM's mathbox to main set.mm
22-Dec-13 inficl    [--same--]  moved from JM's mathbox to main set.mm; revised
22-Dec-13 resoprab2 [--same--]  moved from JM's mathbox to main set.mm
22-Dec-13 oprabval2a ovmpt2x    moved from JM's mathbox to main set.mm; revised
22-Dec-13 eqfnoprv2 [--same--]  moved from JM's mathbox to main set.mm
22-Dec-13 filnetlem5 [--same--] (in JGH's mathbox) revised
22-Dec-13 filnetlem4 [--same--] (in JGH's mathbox) revised
22-Dec-13 filnetlem3 [--same--] (in JGH's mathbox) revised
22-Dec-13 filnetlem2 [--same--] (in JGH's mathbox) revised
22-Dec-13 filnetlem1 [--same--] (in JGH's mathbox) revised
22-Dec-13 tailmap   tailf       (in JGH's mathbox)
22-Dec-13 istail    tailval     (in JGH's mathbox) revised
22-Dec-13 tailf     tailfval    (in JGH's mathbox) revised
22-Dec-13 fmfnfm    [--same--]  (in JGH's mathbox) revised
22-Dec-13 fmfnfmlem4 [--same--] (in JGH's mathbox) revised
22-Dec-13 fmfnfmlem3 [--same--] (in JGH's mathbox) revised
22-Dec-13 fmfnfmlem2 [--same--] (in JGH's mathbox) revised
22-Dec-13 fmfnfmlem1 [--same--] (in JGH's mathbox) revised
22-Dec-13 ufcondr   ufildr      (in JGH's mathbox) revised
22-Dec-13 uffinfix  [--same--]  (in JGH's mathbox) revised
22-Dec-13 fixufil   [--same--]  (in JGH's mathbox) changed variable names
22-Dec-13 uffixfr   [--same--]  (in JGH's mathbox) revised
22-Dec-13 ufileulem ---         (in JGH's mathbox) deleted
22-Dec-13 filssufillem ---      (in JGH's mathbox) deleted
22-Dec-13 supfil    [--same--]  (in JGH's mathbox) revised
22-Dec-13 fbasfip   [--same--]  moved from JGH's mathbox to main set.mm;revised
22-Dec-13 subsubtop ---         (in JGH's mathbox) to be deleted; use subspco
22-Dec-13 ssntr     [--same--]  moved from JGH's mathbox to main set.mm;revised
22-Dec-13 elfiun    [--same--]  moved from JGH's mathbox to main set.mm;revised
22-Dec-13 isrocatset [--same--] (in FL's mathbox) revised
22-Dec-13 df-rocatset [--same--] (in FL's mathbox) revised
22-Dec-13 singcon   ---         (in FL's mathbox) deleted
22-Dec-13 topsinind topsn       moved from FL's mathbox to main set.mm; revised
22-Dec-13 empcon    ---         (in FL's mathbox) deleted
22-Dec-13 intopcon  [--same--]  (in FL's mathbox) revised
22-Dec-13 clindistop [--same--] (in FL's mathbox) revised
22-Dec-13 stfincomp [--same--]  (in FL's mathbox) revised
22-Dec-13 cmptop    [--same--]  (in FL's mathbox) revised
22-Dec-13 subsincomp ---        (in FL's mathbox) deleted
22-Dec-13 subempcomp ---        (in FL's mathbox) deleted
22-Dec-13 limfillem2 ---        (in FL's mathbox) deleted
22-Dec-13 limfillem1 ---        (in FL's mathbox) deleted
22-Dec-13 trnei2    trnei       (in FL's mathbox) revised
22-Dec-13 trfil     [--same--]  (in FL's mathbox) revised
22-Dec-13 rcfpfil   [--same--]  (in FL's mathbox) revised
22-Dec-13 rcfpfillem6 ---       (in FL's mathbox) deleted
22-Dec-13 rcfpfillem5 ---       (in FL's mathbox) deleted
22-Dec-13 rcfpfillem4 ---       (in FL's mathbox) deleted
22-Dec-13 rcfpfillem3 ---       (in FL's mathbox) deleted
22-Dec-13 rcfpfillem2 ---       (in FL's mathbox) deleted
22-Dec-13 rcfpfillem1 ---       (in FL's mathbox) deleted
22-Dec-13 efilcp2   efilcp      (in FL's mathbox) revised
22-Dec-13 efilcp    [--same--]  (in FL's mathbox) revised
22-Dec-13 fgsb      ---         (in FL's mathbox) deleted; use fsubbas,fgfil
22-Dec-13 ptincpw   ---         (in FL's mathbox) deleted; use topgele
22-Dec-13 topge     ---         (in FL's mathbox) deleted; use pwuni
22-Dec-13 topgele   [--same--]  moved from FL's mathbox to main set.mm; revised
22-Dec-13 subtopsin2 subspsn2   moved from FL's mathbox to main set.mm; revised
22-Dec-13 stoig2b   ---         (in FL's mathbox) deleted; use stoig2
22-Dec-13 sbtpsines subspsn     moved from FL's mathbox to main set.mm; revised
22-Dec-13 subspemp2 subsp0      moved from FL's mathbox to main set.mm; revised
22-Dec-13 subspemp  ---         (in FL's mathbox) deleted; use subsp0
22-Dec-13 intopcoaconlem3 [--same--] (in FL's mathbox) revised
22-Dec-13 bintop3   ---         (in FL's mathbox) deleted; use fibas
22-Dec-13 bintop    ---         (in FL's mathbox) deleted; use fibas
22-Dec-13 topindis  ---         (in FL's mathbox) deleted; use topgele
22-Dec-13 rngop     [--same--]  moved from FL's mathbox to main set.mm
22-Dec-13 relcnvfld [--same--]  moved from FL's mathbox to main set.mm
22-Dec-13 ficli     ---         (in FL's mathbox) deleted; use fiin
22-Dec-13 fiiu      ---         (in FL's mathbox) deleted; use fipwuni
22-Dec-13 infi1     ---         (in FL's mathbox) deleted; use fiin
22-Dec-13 mpteq2dvg mpteq2dvgOLD (in FL's mathbox)
22-Dec-13 uzf       [--same--]  moved from SF's mathbox to main set.mm; revised
22-Dec-13 fzf       [--same--]  moved from SF's mathbox to main set.mm; revised
22-Dec-13 elfzm1b   [--same--]  moved from PC's mathbox to main set.mm
22-Dec-13 hashgaddOLD ---       (in PC's mathbox) deleted
22-Dec-13 ---       ---         nmcopexlem1 - nmcopexlem6 deleted
22-Dec-13 eigval1   eigvalval
22-Dec-13 kbvalval  kbval
22-Dec-13 kbval     kbfval      revised
22-Dec-13 bravalval braval
22-Dec-13 braval    brafval     revised
22-Dec-13 cnfnc     [--same--]  revised
22-Dec-13 elnlfn    [--same--]  revised
22-Dec-13 cnopc     [--same--]  revised
22-Dec-13 eigvalval eigvalfval  revised
22-Dec-13 eigvecval [--same--]  revised
22-Dec-13 elcnfn    [--same--]  revised
22-Dec-13 nlfnval   [--same--]  revised
22-Dec-13 dfbdop2   df-bdop
22-Dec-13 elcnop    [--same--]  revised
22-Dec-13 df-spec   [--same--]  revised
22-Dec-13 df-eigval [--same--]  revised
22-Dec-13 df-eigvec [--same--]  revised
22-Dec-13 df-kb     [--same--]  revised
22-Dec-13 df-bra    [--same--]  revised
22-Dec-13 df-lnfn   [--same--]  revised
22-Dec-13 df-cnfn   [--same--]  revised
22-Dec-13 df-nlfn   [--same--]  revised
22-Dec-13 df-nmfn   [--same--]  revised
22-Dec-13 df-hmop   [--same--]  revised
22-Dec-13 df-bdop   [--same--]  revised
22-Dec-13 df-lnop   [--same--]  revised
22-Dec-13 df-cnop   [--same--]  revised
22-Dec-13 df-nmop   [--same--]  revised
22-Dec-13 hfsval    [--same--]  revised
22-Dec-13 hfmmval   [--same--]  revised
22-Dec-13 hfsmval   [--same--]  revised
22-Dec-13 hodmval   [--same--]  revised
22-Dec-13 hommval   [--same--]  revised
22-Dec-13 hosmval   [--same--]  revised
22-Dec-13 df-hfmul  [--same--]  revised
22-Dec-13 df-hsum   [--same--]  revised
22-Dec-13 df-hodif  [--same--]  revised
22-Dec-13 df-homul  [--same--]  revised
22-Dec-13 df-hosum  [--same--]  revised
22-Dec-13 tosdir    [--same--]  revised
22-Dec-13 dirge     [--same--]  changed variable names
22-Dec-13 dirtr     [--same--]  changed variable names
22-Dec-13 dirref    [--same--]  changed variable names
22-Dec-13 dirdm     [--same--]  changed variable names
22-Dec-13 reldir    [--same--]  changed variable names
22-Dec-13 isdir     [--same--]  revised
22-Dec-13 df-tail   [--same--]  revised
22-Dec-13 df-dir    [--same--]  revised
22-Dec-13 contop    [--same--]  revised
22-Dec-13 hausfillim2 hausflim2
22-Dec-13 sflimf    flfval
22-Dec-13 flimff    flffval     revised
22-Dec-13 elfilmap3 elfm3
22-Dec-13 elfilmap2 elfm2
22-Dec-13 elfilmap  elfm
22-Dec-13 fmf       fmfil
22-Dec-13 filmapss  fmss        changed variable names
22-Dec-13 isfilmap  fmval       changed variable names
22-Dec-13 filmapf   fmfval      revised
22-Dec-13 df-flimf  df-flf      revised
22-Dec-13 df-filmap df-fm       revised
22-Dec-13 cflimf    cflf
22-Dec-13 cfilmap   cfm
22-Dec-13 hausfillim hausflim
22-Dec-13 isfillim  elflim
22-Dec-13 limfil    flimval
22-Dec-13 sfvlim    flimfval    revised
22-Dec-13 df-flim1  df-flim     revised
22-Dec-13 cflim1    cflim       revised
22-Dec-13 fbunfip   [--same--]  revised
22-Dec-13 fsubbas   [--same--]  revised
22-Dec-13 infi      fiin        revised
22-Dec-13 0nelfb    [--same--]  revised
22-Dec-13 oefil2    snfil
22-Dec-13 filintf   infil       revised
22-Dec-13 emnfil    [--same--]  revised
22-Dec-13 isfil     isfil2      revised
22-Dec-13 df-fil    [--same--]  revised
22-Dec-13 df-fg     [--same--]  revised
22-Dec-13 stoig3    [--same--]  revised
22-Dec-13 stoigOLD  ---         deleted
22-Dec-13 stoiglem  ---         deleted
22-Dec-13 stoiglemOLD ---       deleted
22-Dec-13 elsubsp   elsubspr    revised
22-Dec-13 issubspt  elsubsp     revised
22-Dec-13 issubsplem1 ---       deleted
22-Dec-13 issubsp   ---         deleted
22-Dec-13 subsp     subspval    revised
22-Dec-13 subspi    [--same--]  revised
22-Dec-13 df-subsp  [--same--]  revised
22-Dec-13 df-homeo  [--same--]  revised
22-Dec-13 fibas     [--same--]  revised
22-Dec-13 fiiu2     fipwuni     revised
22-Dec-13 sppfi     elfi        revised
22-Dec-13 spfi      ---         deleted
22-Dec-13 abfi2     ssfii
22-Dec-13 abfi      ---         deleted
22-Dec-13 inficlALT inficl
22-Dec-13 fine2     fi0         revised
22-Dec-13 fine      ---         deleted
22-Dec-13 fiv       fival       revised
22-Dec-13 df-fi     [--same--]  revised
22-Dec-13 istoset   istoset3    revised
22-Dec-13 df-toset  [--same--]  revised
22-Dec-13 symgval   [--same--]  revised
22-Dec-13 symgoprab ---         deleted
22-Dec-13 df-symgrp df-symg     revised
22-Dec-13 csymgrp   csymg
22-Dec-13 pilem3    [--same--]  revised
22-Dec-13 spwpr4OLD ---         deleted
22-Dec-13 spwex     [--same--]  changed variable names
22-Dec-13 spwcl     [--same--]  changed variable names
22-Dec-13 spwnex    ---         deleted
22-Dec-13 spwval3   ---         deleted
22-Dec-13 spwval    [--same--]  revised
22-Dec-13 spwval2   [--same--]  revised
22-Dec-13 df-spw    [--same--]  revised
22-Dec-13 ipblnfi   [--same--]  revised
22-Dec-13 nmofval   [--same--]  revised
22-Dec-13 lnolin    [--same--]  revised
22-Dec-13 islno     [--same--]  revised
22-Dec-13 lnoval    [--same--]  revised
22-Dec-13 df-hmo    [--same--]  revised
22-Dec-13 df-aj     [--same--]  revised
22-Dec-13 df-0o     [--same--]  revised
22-Dec-13 df-blo    [--same--]  revised
22-Dec-13 df-nmo    [--same--]  revised
22-Dec-13 df-lno    [--same--]  revised
22-Dec-13 df-ssp    [--same--]  revised
22-Dec-13 ipfval    [--same--]  revised
22-Dec-13 df-ip     [--same--]  revised
22-Dec-13 df-ims    [--same--]  revised
22-Dec-13 df-ba     [--same--]  revised
22-Dec-13 opnfval   [--same--]  revised
22-Dec-13 ismsg     ---         deleted
22-Dec-13 mscl      ---         deleted
22-Dec-13 msf       ---         deleted
22-Dec-13 msflem    ---         deleted
22-Dec-13 msrel     ---         deleted
22-Dec-13 df-opn    [--same--]  revised
22-Dec-13 df-ball   [--same--]  revised
22-Dec-13 df-met    [--same--]  revised
22-Dec-13 cnpfval   [--same--]  revised
22-Dec-13 df-cnp    [--same--]  revised
22-Dec-13 df-cn     [--same--]  revised
22-Dec-13 lpfval    [--same--]  revised
22-Dec-13 df-lp     [--same--]  revised
22-Dec-13 neival    [--same--]  revised
22-Dec-13 neifval   [--same--]  revised
22-Dec-13 df-nei    [--same--]  revised
22-Dec-13 ntrval    [--same--]  revised
22-Dec-13 clsfval   [--same--]  revised
22-Dec-13 ntrfval   [--same--]  revised
22-Dec-13 cldval    [--same--]  revised
22-Dec-13 df-cls    [--same--]  revised
22-Dec-13 df-ntr    [--same--]  revised
22-Dec-13 df-cld    [--same--]  revised
22-Dec-13 df-tx     [--same--]  revised
22-Dec-13 df-topgen [--same--]  revised
22-Dec-13 df-top    [--same--]  revised
22-Dec-13 unbenlem  [--same--]  revised
22-Dec-13 df-gcd    [--same--]  revised
22-Dec-13 reeff1o2  reeff1o
22-Dec-13 reeff1o   [--same--]  revised
22-Dec-13 reeff1    [--same--]  revised
22-Dec-13 df-pi     [--same--]  revised
22-Dec-13 df-cos    [--same--]  revised
22-Dec-13 df-sin    [--same--]  revised
22-Dec-13 df-ef     [--same--]  revised
22-Dec-13 cncfval   [--same--]  revised
22-Dec-13 df-cncf   [--same--]  revised
22-Dec-13 climshft2i climshft2  revised
22-Dec-13 climresi  ---         deleted
22-Dec-13 climshfti ---         deleted
22-Dec-13 clim      [--same--]  revised
22-Dec-13 df-clim   [--same--]  revised
22-Dec-13 hashgadd  [--same--]  revised
22-Dec-13 hashenOLDOLD ---      deleted
22-Dec-13 hashenOLD ---         deleted
22-Dec-13 hashfz1OLD ---        deleted
22-Dec-13 hashginvOLD ---       deleted
22-Dec-13 hashgvalOLD ---       deleted
22-Dec-13 hashginv  [--same--]  revised
22-Dec-13 hashgval  [--same--]  revised
22-Dec-13 fz1fiOLD  ---         deleted
22-Dec-13 hashgf1o  [--same--]  revised
22-Dec-13 df-hash   [--same--]  revised
22-Dec-13 bccl2     [--same--]  revised
22-Dec-13 bcpasci   ---         deleted
22-Dec-13 bcpasc2   ---         deleted
22-Dec-13 bcpasc2i  ---         deleted
22-Dec-13 bcnp11    bcn1        revised
22-Dec-13 bccmpl    [--same--]  revised
22-Dec-13 bcval3    [--same--]  revised
22-Dec-13 bcval2    [--same--]  revised
22-Dec-13 bcval     [--same--]  revised
22-Dec-13 df-bc     [--same--]  revised
22-Dec-13 df-abs    [--same--]  revised
22-Dec-13 cjval     remim
22-Dec-13 imval     [--same--]  revised
22-Dec-13 reval     [--same--]  revised
22-Dec-13 df-im     [--same--]  revised
22-Dec-13 df-re     [--same--]  revised
22-Dec-13 df-cj     [--same--]  revised
22-Dec-13 df-limsup [--same--]  revised
22-Dec-13 shftf     [--same--]  revised
22-Dec-13 shftval   [--same--]  revised
22-Dec-13 shftresval ---        deleted
22-Dec-13 shftres   ---         deleted
22-Dec-13 shftfn    [--same--]  revised
22-Dec-13 shftfval  [--same--]  revised
22-Dec-13 df-shft   [--same--]  revised
22-Dec-13 cardfz    [--same--]  revised
22-Dec-13 fzennn    [--same--]  revised
22-Dec-13 uzrdgsuci [--same--]  revised
22-Dec-13 uzrdg0i   [--same--]  revised
22-Dec-13 uzrdgfni  [--same--]  revised
22-Dec-13 uzrdglem  [--same--]  revised
22-Dec-13 om2uzrdg  [--same--]  revised
22-Dec-13 om2uzisoi [--same--]  revised
22-Dec-13 om2uzf1oi [--same--]  revised
22-Dec-13 om2uzrani [--same--]  revised
22-Dec-13 om2uzlt2i [--same--]  revised
22-Dec-13 om2uzlti  [--same--]  revised
22-Dec-13 om2uzuzi  [--same--]  revised
22-Dec-13 om2uzsuci [--same--]  revised
22-Dec-13 om2uz0i   [--same--]  revised
22-Dec-13 df-fz     [--same--]  revised
22-Dec-13 df-uz     [--same--]  revised
22-Dec-13 df-icc    [--same--]  revised
22-Dec-13 df-ico    [--same--]  revised
22-Dec-13 df-ioc    [--same--]  revised
22-Dec-13 df-ioo    [--same--]  revised
22-Dec-13 df-mod    [--same--]  revised
22-Dec-13 df-fl     [--same--]  revised
22-Dec-13 df-div    [--same--]  revised
22-Dec-13 df-sub    [--same--]  revised
22-Dec-13 cflim     cflm
22-Dec-13 cffnon    cff         revised
22-Dec-13 df-cda    [--same--]  revised
22-Dec-13 alephlim  [--same--]  changed variable names
22-Dec-13 df-cf     [--same--]  revised
22-Dec-13 df-aleph  [--same--]  revised
22-Dec-13 df-card   [--same--]  revised
22-Dec-13 df-rank   [--same--]  revised
22-Dec-13 df-r1     [--same--]  revised
22-Dec-13 abfii5    ---         deleted; use dffi2
22-Dec-13 abfii4    ---         deleted; use dffi2
22-Dec-13 abfii3    ---         deleted; use dffi2
22-Dec-13 abfii2    ---         deleted; use dffi2
22-Dec-13 abfii1    ---         deleted; use dffi2
22-Dec-13 df-pm     [--same--]  revised
22-Dec-13 df-map    [--same--]  revised
22-Dec-13 oev2      [--same--]  revised
22-Dec-13 df-oexp   [--same--]  revised
22-Dec-13 df-omul   [--same--]  revised
22-Dec-13 df-oadd   [--same--]  revised
22-Dec-13 frsucmpt2 ---         deleted
22-Dec-13 frsucopab ---         deleted
22-Dec-13 rdglimi   ---         deleted
22-Dec-13 rdgsuci   ---         deleted
22-Dec-13 rdgval    [--same--]  revised
22-Dec-13 rdglem2   ---         deleted
22-Dec-13 dfrdg2    ---         deleted
22-Dec-13 df-rdg    [--same--]  revised
22-Dec-13 tz7.44-3  [--same--]  revised
22-Dec-13 tz7.44-2  [--same--]  revised
22-Dec-13 tz7.44-1  [--same--]  revised
22-Dec-13 foprab2a  [--same--]  revised
22-Dec-13 df-2nd    [--same--]  revised
22-Dec-13 df-1st    [--same--]  revised
22-Dec-13 resmpt2   resmpt
22-Dec-13 mpteq2dvaf mpteq2da
22-Dec-13 mpteqi    mpteq12i
22-Dec-13 oprabval2gfOLD ---    deleted
22-Dec-13 oprabval2gf ---       deleted
22-Dec-13 oprabval2gfNEW oprabval2gf revised
22-Dec-13 oprabvali ---         deleted
22-Dec-13 oprabvaligg [--same--] revised
22-Dec-13 oprabvalig [--same--] revised
25-Nov-13 eq2ab     ---         obsolete; use abbi instead
14-Nov-13 sb19.21   sbrim
11-Nov-13 alrot3    [--same--]  moved from ATS's mathbox to main set.mm
11-Nov-13 pm11.53   [--same--]  moved from ATS's mathbox to main set.mm
 4-Nov-13 ispos     [--same--]  removed nonempty base set requirement
 4-Nov-13 df-poset  [--same--]  removed nonempty base set requirement
17-Oct-13 mpt2eqdv  mpt2eqdva
17-Oct-13 mpt2eqdvg mpt2eqdvaf  moved from FL's mathbox to main set.mm
 6-Oct-13 ipid      ipidsq
 5-Oct-13 plusgval  ---         obsolete; use grpplusg
 5-Oct-13 divrngmgrp [--same--] eliminated hard-coded structure indices
 5-Oct-13 divrngid  [--same--]  eliminated hard-coded structure indices
 5-Oct-13 divrngidlem [--same--] eliminated hard-coded structure indices
 5-Oct-13 invrfval  [--same--]  eliminated hard-coded structure indices
 5-Oct-13 divrngid  [--same--]  eliminated hard-coded structure indices
 5-Oct-13 divrngidlem [--same--] eliminated hard-coded structure indices
 5-Oct-13 divrngmgrp [--same--] eliminated hard-coded structure indices
 5-Oct-13 isdivrng  [--same--]  eliminated hard-coded structure indices
 5-Oct-13 df-drng   [--same--]  eliminated hard-coded structure indices
 5-Oct-13 ndxargi   ndxarg
 5-Oct-13 strcval   strfvn
 3-Oct-13 ringmulr  rngmulr     eliminated unnecessary hypotheses
 3-Oct-13 ringplusg rngplusg    eliminated unnecessary hypotheses
 3-Oct-13 ringbase  rngbase     eliminated unnecessary hypotheses
 3-Oct-13 grpplusgg ---         obsolete; use grpplusg
 3-Oct-13 grpbaseg  ---         obsolete; use grpbase
 3-Oct-13 grpplusg  [--same--]  eliminated unnecessary antecedent
 3-Oct-13 grpbase   [--same--]  eliminated unnecessary antecedent
 3-Oct-13 str3v3    ---         obsolete; use strfv
 3-Oct-13 str3v2    ---         obsolete; use strfv
 3-Oct-13 str3v1    ---         obsolete; use strfv
 3-Oct-13 str2v2    ---         obsolete; use strfv
 3-Oct-13 str2v1    ---         obsolete; use strfv
 3-Oct-13 str3v3x   ---         obsolete; use strfv
 3-Oct-13 str3v2x   ---         obsolete; use strfv
 3-Oct-13 str3v1x   ---         obsolete; use strfv
 3-Oct-13 str2v2x   ---         obsolete; use strfv
 3-Oct-13 str2v1x   ---         obsolete; use strfv
 3-Oct-12 tpshyp    ---         obsolete; use tpslem
 3-Oct-13 ringhyp   ---         obsolete; use rnglem
 3-Oct-13 grphyp    ---         obsolete; use grplem
 3-Oct-13 poshyp    ---         obsolete; use poslem
 3-Oct-13 poslem    posi
 2-Oct-13 isfinite  ---         obsolete; use isfinite3
 1-Oct-13 ressnop0  [--same--]  eliminated unnecessary hypotheses
 1-Oct-13 fvtp3     [--same--]  eliminated unnecessary hypotheses
 1-Oct-13 fvtp2     [--same--]  eliminated unnecessary hypotheses
 1-Oct-13 fvtp1     [--same--]  eliminated unnecessary hypotheses
 1-Oct-13 fvpr2     [--same--]  eliminated unnecessary hypotheses
 1-Oct-13 fvpr1     [--same--]  eliminated unnecessary hypotheses
 1-Oct-13 fntp      [--same--]  eliminated unnecessary hypotheses
 1-Oct-13 fnprg     [--same--]  eliminated unnecessary antecedents
 1-Oct-13 fnsn      [--same--]  eliminated unnecessary hypothesis
 1-Oct-13 funtp     [--same--]  eliminated unnecessary hypotheses
 1-Oct-13 funpr     [--same--]  eliminated unnecessary hypotheses
 1-Oct-13 funprg    [--same--]  eliminated unnecessary antecedents
 1-Oct-13 funsng    [--same--]  eliminated unnecessary antecedent
 1-Oct-13 funsn     [--same--]  eliminated unnecessary hypothesis
30-Sep-13 ltneii    [--same--]  swapped conclusion vars for ltnei compatibility
25-Sep-13 2nalexn   [--same--]  moved from ATS's mathbox to main set.mm
25-Sep-13 2exnexn   [--same--]  moved from ATS's mathbox to main set.mm
24-Sep-13 supeq2    [--same--]  moved from JM's mathbox to main set.mm
24-Sep-13 ixpfi     [--same--]  moved from JM's mathbox to main set.mm
24-Sep-13 mapfi     [--same--]  moved from JM's mathbox to main set.mm
24-Sep-13 enf1f1o   fienf1f1o   moved from JM's mathbox to main set.mm
24-Sep-13 nnaun2    ficardun2
24-Sep-13 nnaun     ficardun
24-Sep-13 relsn     relsnop
24-Sep-13 difdisj   disjdif
20-Sep-13 imdistanda [--same--] moved from JM's mathbox to main set.mm
20-Sep-13 rnoprab2  [--same--]  moved from SF's mathbox to main set.mm
20-Sep-13 eqfunfv   [--same--]  moved from SF's mathbox to main set.mm
20-Sep-13 pm5.21ndd [--same--]  moved from PC's mathbox to main set.mm
20-Sep-13 div2neg   [--same--]  moved from PC's mathbox to main set.mm
16-Sep-13 oprabexd  [--same--]  moved from JM's mathbox to main set.mm
16-Sep-13 fsum00    [--same--]  moved from JM's mathbox to main set.mm
16-Sep-13 fzdisj    [--same--]  moved from JM's mathbox to main set.mm
16-Sep-13 fzsplit   [--same--]  moved from JM's mathbox to main set.mm
16-Sep-13 fzn0      [--same--]  moved from JM's mathbox to main set.mm
16-Sep-13 fz10      [--same--]  moved from JM's mathbox to main set.mm
16-Sep-13 addsubeq4 [--same--]  moved from JM's mathbox to main set.mm
16-Sep-13 add20     [--same--]  moved from JM's mathbox to main set.mm
16-Sep-13 f1elima   [--same--]  moved from JM's mathbox to main set.mm
15-Sep-13 hashpw    [--same--]  moved from PC's mathbox to main set.mm
15-Sep-13 hashpwlem [--same--]  moved from PC's mathbox to main set.mm
15-Sep-13 hashxp    [--same--]  moved from PC's mathbox to main set.mm
15-Sep-13 hashxplem [--same--]  moved from PC's mathbox to main set.mm
15-Sep-13 hashunsng [--same--]  moved from PC's mathbox to main set.mm
15-Sep-13 hashun    [--same--]  moved from PC's mathbox to main set.mm
15-Sep-13 hashgadd  [--same--]  moved from PC's mathbox to main set.mm
15-Sep-13 2ne3      ---         obsolete (use 2lt3 + ltneii instead)
15-Sep-13 1ne9      ---         obsolete (use 1lt9 + ltneii instead)
15-Sep-13 1ne3      ---         obsolete (use 1lt3 + ltneii instead)
10-Sep-13 exp5c     [--same--]  moved from JGH's mathbox to main set.mm
10-Sep-13 snelpwr   snelpwi     moved from AS's mathbox to main set.mm
 8-Sep-13 df-exp    [--same--]  revised definition
 8-Sep-13 df-fac    [--same--]  revised definition
 8-Sep-13 df-seq0   [--same--]  revised definition
 8-Sep-13 df-seq1   [--same--]  revised definition
 8-Sep-13 df-seqz   [--same--]  revised definition
 8-Sep-13 df-sqr    [--same--]  revised definition
 8-Sep-13 expval    [--same--]  revised theorem statement
 8-Sep-13 facnn     [--same--]  revised theorem statement
 8-Sep-13 fzp1ss    [--same--]  revised theorem statement
 8-Sep-13 fzss1     [--same--]  revised theorem statement
 8-Sep-13 fzss2     [--same--]  revised theorem statement
 8-Sep-13 fzssp1    [--same--]  revised theorem statement
 8-Sep-13 om2uzf1oi [--same--]  revised theorem statement
 8-Sep-13 om2uzisoi [--same--]  revised theorem statement
 8-Sep-13 om2uzrani [--same--]  revised theorem statement
 8-Sep-13 om2uzuzi  [--same--]  revised theorem statement
 8-Sep-13 seq0fval  [--same--]  revised theorem statement
 8-Sep-13 seqzfval  [--same--]  revised theorem statement
 8-Sep-13 sqrlem1   [--same--]  revised theorem statement
 8-Sep-13 sqrlem2   [--same--]  revised theorem statement
 8-Sep-13 sqrlem3   [--same--]  revised theorem statement
 8-Sep-13 sqrlem4   [--same--]  revised theorem statement
 8-Sep-13 sqrlem5   [--same--]  revised theorem statement
 8-Sep-13 sqrlem6   [--same--]  revised theorem statement
 8-Sep-13 sqrlem7   [--same--]  revised theorem statement
 8-Sep-13 sqrval    [--same--]  revised theorem statement
 8-Sep-13 uzrdgsuci [--same--]  revised theorem statement
 8-Sep-13 sqrcl     resqrcl     (new sqrcl is complex version)
 8-Sep-13 dfseq0    ---         obsolete
 8-Sep-13 expnnval  ---         obsolete
 8-Sep-13 seq0valt  ---         obsolete
 8-Sep-13 seq11lem  ---         obsolete
 8-Sep-13 seq1fnlem ---         obsolete
 8-Sep-13 seq1lem1  ---         obsolete
 8-Sep-13 seq1rval  ---         obsolete
 8-Sep-13 seq1seq0  ---         obsolete
 8-Sep-13 seq1seq01 ---         obsolete
 8-Sep-13 seq1seq02 ---         obsolete
 8-Sep-13 seq1suclem ---        obsolete
 8-Sep-13 seq1val   ---         obsolete
 8-Sep-13 seq1val2  ---         obsolete
 8-Sep-13 seqzfval2 ---         obsolete
 8-Sep-13 seqzval   ---         obsolete
 8-Sep-13 seqzval2  ---         obsolete
 8-Sep-13 ---       ---         sqrlem10 - sqrlem24 and sqrlem26 obsolete
 8-Sep-13 sqrlem8   ---         obsolete
 8-Sep-13 sqrlem9   ---         obsolete
 8-Sep-13 uzrdgfnuzi ---        obsolete
 8-Sep-13 uzrdginii ---         obsolete
 8-Sep-13 uzrdginip1i ---       obsolete
 8-Sep-13 uzrdgvali ---         obsolete
 8-Sep-13 ---       ---         math token "seq" changed to "seqz"
 2-Sep-13 ltfrn     [--same--]  revised theorem statement
 2-Sep-13 ltfrn     [--same--]  moved from ATS's mathbox to main set.mm
 2-Sep-13 eluzsub   [--same--]  moved from JM's mathbox to main set.mm
 2-Sep-13 eluzadd   [--same--]  moved from JM's mathbox to main set.mm
 2-Sep-13 rdgeq12   [--same--]  moved from SF's mathbox to main set.mm
 1-Sep-13 raffsp    craffsp     (in FL's mathbox)
 1-Sep-13 ptdfc     cptdfc      (in ATS's mathbox)
 1-Sep-13 rr3c      crr3c       (in ATS's mathbox)
 1-Sep-13 psc       cpsc        (in NM's mathbox)
 1-Sep-13 wgcdOLD   cgcdOLD     (in JH's mathbox)
 1-Sep-13 plusrc    cplusr      (in ATS's mathbox)
 1-Sep-13 minusrc   cminusr     (in ATS's mathbox)
 1-Sep-13 timesrc   ctimesr     (in ATS's mathbox)
 1-Sep-13 csmo      wsmo
 1-Sep-13 syn-bnj17 w-bnj17     (in JBN's mathbox)
 1-Sep-13 syn-bnj16 c-bnj16     (in JBN's mathbox)
 1-Sep-13 syn-bnj14 c-bnj14     (in JBN's mathbox)
 1-Sep-13 syn-bnj13 w-bnj13     (in JBN's mathbox)
 1-Sep-13 syn-bnj15 w-bnj15     (in JBN's mathbox)
 1-Sep-13 syn-bnj18 c-bnj18     (in JBN's mathbox)
 1-Sep-13 syn-bnj19 w-bnj19     (in JBN's mathbox)
 1-Sep-13 vd1       wvd1        (in AS's mathbox)
 1-Sep-13 vd2       wvd2        (in AS's mathbox)
 1-Sep-13 vd3       wvd3        (in AS's mathbox)
31-Aug-13 trcl-df   df-trcl     (in FL's mathbox)
31-Aug-13 rtrcl-df  df-rtrcl    (in FL's mathbox)
31-Aug-13 orHom-df  df-orHom    (in FL's mathbox)
31-Aug-13 orIso-df  df-orIso    (in FL's mathbox)
31-Aug-13 decfun-df df-decfun   (in FL's mathbox)
31-Aug-13 expsg-df  df-expsg    (in FL's mathbox)
29-Aug-13 clsbldneg notab       moved from FL's mathbox to main set.mm
18-Aug-13 oprabval2gf [--same--] added bound var hypotheses
10-Aug-13 vtocl2gf  [--same--]  added bound var hypotheses
 7-Aug-13 ringidval [--same--]  changed iota to iota_
 7-Aug-13 df-1r     [--same--]  changed iota to iota_
 7-Aug-13 grpidcl   [--same--]  changed variable names
 7-Aug-13 grpid     [--same--]  changed variable names
 7-Aug-13 grpinveu  [--same--]  changed variable names
 7-Aug-13 grpinvid  [--same--]  changed variable names
 7-Aug-13 grpinvid2 [--same--]  changed variable names
 7-Aug-13 grpinvid1 [--same--]  changed variable names
 7-Aug-13 grprinv   [--same--]  changed variable names
 7-Aug-13 grplinv   [--same--]  changed variable names
 7-Aug-13 grpinv    [--same--]  changed variable names
 7-Aug-13 grpinvval [--same--]  changed iota to iota_
 7-Aug-13 grpinvfval [--same--] changed iota to iota_
 7-Aug-13 df-minusg [--same--]  changed iota to iota_
 7-Aug-13 grprid    [--same--]  changed variable names
 7-Aug-13 grplid    [--same--]  changed variable names
 7-Aug-13 grpidinv2 [--same--]  changed variable names
 7-Aug-13 grpidval  [--same--]  changed iota to iota_
 7-Aug-13 df-0g     [--same--]  changed iota to iota_
 6-Aug-13 isabld    isablod     (in JM's mathbox)
 2-Aug-13 isringd   isringod    (in JM's mathbox)
30-Jul-13 riemtn    mptresid    moved from FL's mathbox to main set.mm
30-Jul-13 riecb     opabresid   moved from FL's mathbox to main set.mm
25-Jul-13 sbcne12g  [--same--]  moved from ATS's mathbox to main set.mm
25-Jul-13 sbcnel12g [--same--]  moved from ATS's mathbox to main set.mm
17-Jul-13 fvopab4s  [--same--]  eliminated redundant hypothesis
30-Jun-13 bnj1263   syl5sseqr   moved from JBN's mathbox to main set.mm
30-Jun-13 bnj1264   syl5sseq    moved from JBN's mathbox to main set.mm
30-Jun-13 bnj1141   syl6ss      moved from JBN's mathbox to main set.mm
24-Jun-13 onsubcum  onssr1      moved from FL's mathbox to main set.mm
21-Jun-13 19.40-2   [--same--]  moved from ATS's mathbox to main set.mm
21-Jun-13 hbxfr     hbxfreq
21-Jun-13 ssopab2   ssopab2b
18-Jun-13 boe       enpr1g      moved from FL's mathbox to main set.mm
18-Jun-13 unpde2eg2 pr2nelem    moved from FL's mathbox to main set.mm
18-Jun-13 unpde2eg22 pr2ne      moved from FL's mathbox to main set.mm
18-Jun-13 unpam2    prdom2      moved from FL's mathbox to main set.mm
18-Jun-13 uncum     r1tr2       moved from FL's mathbox to main set.mm
18-Jun-13 ctarski   ctsk        moved from FL's mathbox to main set.mm
18-Jun-13 cgruni    cgru        moved from FL's mathbox to main set.mm
18-Jun-13 df-tsk    [--same--]  moved from FL's mathbox to main set.mm
18-Jun-13 taralt    dftsk2      moved from FL's mathbox to main set.mm
18-Jun-13 tarval    eltsk       moved from FL's mathbox to main set.mm
18-Jun-13 tarvalg   eltskg      moved from FL's mathbox to main set.mm
18-Jun-13 tarval1   eltsk2      moved from FL's mathbox to main set.mm
18-Jun-13 tarval1g  eltsk2g     moved from FL's mathbox to main set.mm
18-Jun-13 tarax1    tskpwss     moved from FL's mathbox to main set.mm
18-Jun-13 tarax2    tskpw       moved from FL's mathbox to main set.mm
18-Jun-13 tarax3    tsken       moved from FL's mathbox to main set.mm
18-Jun-13 empistar  0tsk        moved from FL's mathbox to main set.mm
18-Jun-13 tarax3d2  tsksdom     moved from FL's mathbox to main set.mm
18-Jun-13 tarax3e   tskssel2    moved from FL's mathbox to main set.mm
18-Jun-13 tarax3f   tskssel     moved from FL's mathbox to main set.mm
18-Jun-13 tarsin    tsksn       moved from FL's mathbox to main set.mm
18-Jun-13 emptar    tsk0        moved from FL's mathbox to main set.mm
18-Jun-13 tarone    tsk1        moved from FL's mathbox to main set.mm
18-Jun-13 tartwo    tsk2        moved from FL's mathbox to main set.mm
18-Jun-13 tarmrtwo  2domtsk     moved from FL's mathbox to main set.mm
18-Jun-13 tarunpa   tskpr       moved from FL's mathbox to main set.mm
18-Jun-13 tarorpa   tskop       moved from FL's mathbox to main set.mm
18-Jun-13 tarcrpr   tskxpss     moved from FL's mathbox to main set.mm
18-Jun-13 ixpssmapg [--same--]  moved from JM's mathbox to main set.mm
18-Jun-13 bnj572    hbxfrbi     moved from JBN's mathbox to main set.mm
 5-Jun-13 isgrpd    isgrpod     (in JM's mathbox)
24-May-13 pm2.01bd  pm2.18d     moved from FL's mathbox to main set.mm
23-May-13 r19.3zvb  r19.3z      moved from FL's mathbox to main set.mm
22-May-13 son2lpi   [--same--]  eliminated redundant hypotheses
22-May-13 sotri     [--same--]  eliminated redundant hypotheses
22-May-13 soirri    [--same--]  eliminated redundant hypothesis
22-May-13 suprnubii [--same--]  eliminated redundant hypothesis
22-May-13 suprleubii [--same--]  eliminated redundant hypothesis
20-May-13 suprnub   [--same--]  eliminated redundant antecedent
20-May-13 suprleub  [--same--]  eliminated redundant antecedent
20-May-13 noinfep   [--same--]  eliminated redundant antecedent
18-May-13 pre-axlttri axpre-lttri
18-May-13 pre-axlttrn axpre-lttrn
18-May-13 pre-axltadd axpre-ltadd
18-May-13 pre-axmulgt0 axpre-mulgt0
18-May-13 pre-axsup  axpre-sup
16-May-13 3ne0      [--same--]  moved from FL's mathbox to main set.mm
16-May-13 3cn       [--same--]  moved from FL's mathbox to main set.mm
16-May-13 ltaddpos2tb ltaddrp   moved from FL's mathbox to main set.mm
16-May-13 ltsubpostb ltsubrp    moved from FL's mathbox to main set.mm
16-May-13 r19.26t   r19.26-3    moved from FL's mathbox to main set.mm
16-May-13 uzp1      [--same--]  moved from JM's mathbox to main set.mm
16-May-13 uzm1      [--same--]  moved from JM's mathbox to main set.mm
16-May-13 r1subsuc  r1sssuc     moved from FL's mathbox to main set.mm
15-May-13 impbidd   [--same--]  moved from RM's mathbox to main set.mm
26-Apr-13 domint    dmiin       moved from FL's mathbox to main set.mm
26-Apr-13 inpartelt iinss2      moved from FL's mathbox to main set.mm
25-Apr-13 ssiing    ssiinf      moved from FL's mathbox to main set.mm
24-Apr-13 cnvintcnv cnviin      moved from FL's mathbox to main set.mm
23-Apr-13 eqrelrivg eqrelriv    moved from FL's mathbox to main set.mm
23-Apr-13 eqrelriv  eqrelriiv
22-Apr-13 coeq12d   [--same--]  moved from FL's mathbox to main set.mm
21-Apr-13 coeq12i   [--same--]  moved from FL's mathbox to main set.mm
20-Apr-13 cexint2   iinexg      moved from FL's mathbox to main set.mm
19-Apr-13 fnimapr   [--same--]  moved from JM's mathbox to main set.mm
18-Apr-13 foco2     [--same--]  moved from JM's mathbox to main set.mm
17-Apr-13 pm11.07   [--same--]  moved from ATS's mathbox to main set.mm
16-Apr-13 rcla4t    [--same--]  moved from ATS's mathbox to main set.mm
15-Apr-13 cla4gft   [--same--]  moved from ATS's mathbox to main set.mm
14-Apr-13 isseta    issetf      moved from ATS's mathbox to main set.mm
12-Apr-13 orkurss   opid        moved from FL's mathbox to main set.mm
11-Apr-13 cmpinj    f1cocnv1    moved from FL's mathbox to main set.mm
11-Apr-13 cmpinj2   f1cocnv2    moved from FL's mathbox to main set.mm
10-Apr-13 cnvinj    f1cnv       moved from FL's mathbox to main set.mm
10-Apr-13 f1cnv     f1cnvcnv
 9-Apr-13 reltrncnv relcnvtr    moved from FL's mathbox to main set.mm
 9-Apr-13 fmptd     [--same--]  added "F =" hypothesis
 9-Apr-13 fnmpt     funmpt
 8-Apr-13 cnveq2    cnveqb      moved from FL's mathbox to main set.mm
 7-Apr-13 prnzg     [--same--]  moved from FL's mathbox to main set.mm
 6-Apr-13 resrelfld relresfld   moved from FL's mathbox to main set.mm
 5-Apr-13 cmprelid2 relcoi1     moved from FL's mathbox to main set.mm
 5-Apr-13 cmprelid1 relcoi2     moved from FL's mathbox to main set.mm
 5-Apr-13 inclrel   coss1       moved from FL's mathbox to main set.mm
 5-Apr-13 cmpdia    coires1     moved from FL's mathbox to main set.mm
 4-Apr-13 findcard2s [--same--]  moved from PC's mathbox to main set.mm
 3-Apr-13 prmexpb   [--same--]  moved from PC's mathbox to main set.mm
 3-Apr-13 prmdvdsexpb [--same--]  moved from PC's mathbox to main set.mm
 2-Apr-13 imimorb   [--same--]  moved from PC's mathbox to main set.mm
 1-Apr-13 ac6sg     [--same--]  antecedent now has V instead of _V
 1-Apr-13 clint3    ---         obsolete; use icccld instead
 1-Apr-13 clicls    icccld
 1-Apr-13 lemul2aALT ---        obsolete; use lemul2a instead
 1-Apr-13 cdrci     difreicc
 1-Apr-13 rabeq0    [--same--]  moved from JM's mathbox to main set.mm
31-Mar-13 difin2    [--same--]  moved from JM's mathbox to main set.mm
30-Mar-13 respreima [--same--]  moved from JM's mathbox to main set.mm
29-Mar-13 unpreima  [--same--]  moved from JM's mathbox to main set.mm
28-Mar-13 inpreima  [--same--]  moved from JM's mathbox to main set.mm
27-Mar-13 elpri     [--same--]  moved from SF's mathbox to main set.mm
26-Mar-13 indifdi   indifdir    moved from SF's mathbox to main set.mm
25-Mar-13 r19.30    [--same--]  moved from SF's mathbox to main set.mm
24-Mar-13 r19.21    [--same--]  moved from SF's mathbox to main set.mm
23-Mar-13 19.41vvvv [--same--]  moved from FL's mathbox to main set.mm
23-Mar-13 disjr     [--same--]  moved from JM's mathbox to main set.mm
22-Mar-13 smores2   smores3
22-Mar-13 soxp      [--same--]  changed hypotheses to antecedents
22-Mar-13 poxp      [--same--]  changed hypotheses to antecedents
22-Mar-13 frxp      [--same--]  changed hypotheses to antecedents
22-Mar-13 wexp      [--same--]  changed hypotheses to antecedents
22-Mar-13 soxp      [--same--]  moved from SF's mathbox to main set.mm
22-Mar-13 poxp      [--same--]  moved from SF's mathbox to main set.mm
22-Mar-13 frxp      [--same--]  moved from SF's mathbox to main set.mm
22-Mar-13 wexp      [--same--]  moved from SF's mathbox to main set.mm
22-Mar-13 mapdom1   [--same--]  removed redundant hypothesis
22-Mar-13 mapen     [--same--]  removed redundant hypotheses
22-Mar-13 mapsnen   [--same--]  removed redundant hypothesis
22-Mar-13 xpen      [--same--]  removed redundant hypotheses
22-Mar-13 xpeng     [--same--]  removed redundant antecedents
21-Mar-13 3reeanv   [--same--]  moved from JM's mathbox to main set.mm
20-Mar-13 rexrab    [--same--]  moved from JM's mathbox to main set.mm
19-Mar-13 ee01      mpsyl       moved from AS's mathbox to main set.mm
19-Mar-13 morex     [--same--]  moved from JM's mathbox to main set.mm
18-Mar-13 cbviota   [--same--]  moved from ATS's mathbox to main set.mm
18-Mar-13 cbviotaf  [--same--]  moved from ATS's mathbox to main set.mm
17-Mar-13 raleqfn   [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 xporderlem [--same--]  moved from SF's mathbox to main set.mm
16-Mar-13 3an6      [--same--]  moved from SF's mathbox to main set.mm
16-Mar-13 3or6      [--same--]  moved from SF's mathbox to main set.mm
16-Mar-13 elres     [--same--]  moved from SF's mathbox to main set.mm
16-Mar-13 elsnres   [--same--]  moved from SF's mathbox to main set.mm
16-Mar-13 issmo     [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smoeq     [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smodm     [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smores    [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smores3   [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 iordsmo   [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smo0      [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smofvon   [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smoel     [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smoiun    [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smoiso    [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 smoge     [--same--]  moved from ATS's mathbox to main set.mm
16-Mar-13 supeut    [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 fisup2g   [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 fimax2g   [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 wofi      [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 frfi      [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 pofun     [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 frminex   [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 xpeng     [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 fimax     [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 fimaxg    [--same--]  moved from JM's mathbox to main set.mm
16-Mar-13 fisupg    [--same--]  moved from JM's mathbox to main set.mm
15-Mar-13 trint0    [--same--]  moved from ATS's mathbox to main set.mm
15-Mar-13 ordintdif [--same--]  moved from ATS's mathbox to main set.mm
14-Mar-13 ne0f      n0f
 1-Mar-13 eupickbi  [--same--]  moved from ATS's mathbox to main set.mm
 1-Mar-13 dvelimfALT2 [--same--] moved from ATS's mathbox to main set.mm
 1-Mar-13 ax12      a12study2   moved from ATS's mathbox to main set.mm
24-Feb-13 sbceq2dig sbceq2g
24-Feb-13 sbceq1dig sbceq1g
24-Feb-13 sbceqdig  sbceqg
24-Feb-13 sbcbidig  sbcbig
21-Feb-13 ---       ---         See http://us.metamath.org/mpegif/mmnotes.txt
21-Feb-13 ---       ---         entry of 21-Feb-13 for instructions for
21-Feb-13 ---       ---         the changes below.
21-Feb-13 sylan     [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylanb    [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylanbr   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylan2    [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylan2b   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylan2br  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl2an    [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl2anb   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl2anbr  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syland    [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylan2d   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl2and   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylanl1   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylanl2   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylanr1   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylanr2   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylani    [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylan2i   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl2ani   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylancl   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylancr   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylanbrc  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylancb   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 sylancbr  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an1   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an2   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an3   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an1b  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an2b  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an3b  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an1br [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an2br [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an3br [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3an    [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3anb   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3anbr  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syld3an3  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syld3an1  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syld3an2  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3anl1  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3anl2  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3anl3  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3anl   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3anr1  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3anr2  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl3anr3  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5com   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5      [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5d     [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5ib    syl5bi      reordered hypotheses for better logical flow
21-Feb-13 syl5ibr   syl5bir     reordered hypotheses for better logical flow
21-Feb-13 syl5bi    syl5ib      reordered hypotheses for better logical flow
21-Feb-13 syl5cbi   syl5ibcom   reordered hypotheses for better logical flow
21-Feb-13 syl5bir   syl5ibr     reordered hypotheses for better logical flow
21-Feb-13 syl5cbir  syl5ibrcom  reordered hypotheses for better logical flow
21-Feb-13 syl5bb    [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5rbb   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5bbr   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5rbbr  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5eq    [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5req   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5eqr   [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5reqr  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5eqel  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5eqelr [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5eleq  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5eleqr [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5eqner [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5ss    syl5eqss    reordered hypotheses for better logical flow
21-Feb-13 syl5ssr   syl5eqssr   reordered hypotheses for better logical flow
21-Feb-13 syl5eqbr  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5eqbrr [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5breq  [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl5breqr [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl7      [--same--]  reordered hypotheses for better logical flow
21-Feb-13 syl7ib    syl7bi      reordered hypotheses for better logical flow
21-Feb-13 syl6ss    syl6sseq
21-Feb-13 syl6ssr   syl6sseqr
19-Feb-13 fv4       fv4         moved from ATS's mathbox to main set.mm
11-Feb-13 fvopab2b  fvmpt2      moved from FL's mathbox to main set.mm
11-Feb-13 isfinite3 [--same--]  moved from FL's mathbox to main set.mm
 4-Feb-13 remcon    difabs      moved from FL's mathbox to main set.mm
 4-Feb-13 foelrn    [--same--]  moved from JM's mathbox to main set.mm
 4-Feb-13 xpeq2d    [--same--]  moved from JM's mathbox to main set.mm
 4-Feb-13 xpeq1d    [--same--]  moved from JM's mathbox to main set.mm
31-Jan-13 opabex3   [--same--]  moved from JM's mathbox to main set.mm
31-Jan-13 ressn0    ressnop0    moved from SF's mathbox to main set.mm
31-Jan-13 valfunun  fvun        moved from FL's mathbox to main set.mm
20-Jan-13 sucdomi   ---         obsolete; use sucdom instead
20-Jan-13 omsucdom  ---         obsolete; use sucdom instead
20-Jan-13 fisucdom  ---         obsolete; use sucdom instead
20-Jan-13 cardennn  [--same--]  eliminated redundant antecedent
20-Jan-13 oncardon  ---         obsolete; use cardon instead
20-Jan-13 weth      [--same--]  made hypothesis into antecedent
20-Jan-13 tz7.49    [--same--]  changed hypotheses
20-Jan-13 tz7.49c   [--same--]  changed hypotheses
20-Jan-13 r19.23aivr r19.23aivw  moved from FL's mathbox to main set.mm
 4-Jan-13 mul23     mul32
 4-Jan-13 mul23i    mul32i
 4-Jan-13 add23     add32
 4-Jan-13 add23i    add32i
 4-Jan-13 cbvralcsf [--same--]  moved from ATS's mathbox to main set.mm
 4-Jan-13 cbvrexcsf [--same--]  moved from ATS's mathbox to main set.mm
 4-Jan-13 cbvreucsf [--same--]  moved from ATS's mathbox to main set.mm
 4-Jan-13 cbvrabcsf [--same--]  moved from ATS's mathbox to main set.mm
 3-Jan-13 ax0id     addid1
 3-Jan-13 ax1id     mulid1
10-Dec-12 elimant   ---         obsolete (renamed elimantOLD, to be deleted)
 1-Dec-12 fixp      xpfi
 1-Dec-12 xpfi      xpfir
 1-Dec-12 finsucdom fisucdom
 1-Dec-12 setwoe    en1eqsn
 1-Dec-12 sfseqeq   fisseneq
 1-Dec-12 islfin    difinf
 1-Dec-12 unfin     unfir
 1-Dec-12 finfin    diffi
 1-Dec-12 twpar2    uneqdifeq
 1-Dec-12 findcard2 [--same--]  moved from JM's mathbox to main set.mm
27-Nov-12 an1s      an12s
27-Nov-12 an1rs     an32s
27-Nov-12 ancom13s  an13s
27-Nov-12 ancom31s  an31s
19-Nov-12 ee11      ---         obsolete; same as sylc
17-Nov-12 seq11g    [--same--]  moved from JM's mathbox to main set.mm
17-Nov-12 seq1p1g   [--same--]  moved from JM's mathbox to main set.mm
17-Nov-12 seqz1g    [--same--]  moved from JM's mathbox to main set.mm
17-Nov-12 seqzp1g   [--same--]  moved from JM's mathbox to main set.mm
17-Nov-12 seq1seqzg [--same--]  moved from JM's mathbox to main set.mm
16-Nov-12 ordelordaxr ordelordALT
12-Nov-12 funimadisj fnimadisj
 4-Nov-12 ---       ---         math token "0vNEW" changed to "0v"
 4-Nov-12 ---       ---         math token "0v" changed to "0vec"
 4-Nov-12 ---       ---         math token "1rNEW" changed to "1r"
 4-Nov-12 ---       ---         math token "TopSet" changed to "TopOpen"
 4-Nov-12 ---       ---         math token "Toset" changed to "TosetRel"
 4-Nov-12 ---       ---         math token "Dir" changed to "DirRel"
 4-Nov-12 ---       ---         math token "LatNEW" changed to "Lat"
 4-Nov-12 ---       ---         math token "Lat" changed to "LatRel"
 4-Nov-12 ---       ---         math token "PosetNEW" changed to "Poset"
 4-Nov-12 ---       ---         math token "Poset" changed to "PosetRel"
 4-Nov-12 ---       ---         math token "DivRingNEW" changed to "DivRing"
 4-Nov-12 ---       ---         math token "DivRing" changed to "DivRingOps"
 4-Nov-12 ---       ---         math token "RingNEW" changed to "Ring"
 4-Nov-12 ---       ---         math token "Ring" changed to "RingOps"
 4-Nov-12 ---       ---         math token "SubGrp" changed to "SubGrpOp"
 4-Nov-12 ---       ---         math token "AbelNEW" changed to "Abel"
 4-Nov-12 ---       ---         math token "Abel" changed to "AbelOp"
 4-Nov-12 ---       ---         math token "GrpNEW" changed to "Grp"
 4-Nov-12 ---       ---         math token "Grp" changed to "GrpOp"
 4-Nov-12 ---       ---         math token "Open" changed to "MetOpen"
 4-Nov-12 grpNEW2grp grp2grpo
 4-Nov-12 grpNEWstr grpstr
 4-Nov-12 grpNEWprop grpprop
 4-Nov-12 grp2grpNEW grp2grp
 4-Nov-12 postrNEW  postr
 4-Nov-12 isdivrngNEW isdivrng
 4-Nov-12 df-drngNEW df-drng
 4-Nov-12 cdivringNEW cdivring
 4-Nov-12 ringrzNEW ringrz
 4-Nov-12 ringlzNEW ringlz
 4-Nov-12 ringridmNEW ringridm
 4-Nov-12 ringlidmNEW ringlidm
 4-Nov-12 ringidmlemNEW ringidmlem
 4-Nov-12 ringgrpNEW ringgrp
 4-Nov-12 ringablNEW ringabl
 4-Nov-12 ringdirNEW ringdir
 4-Nov-12 ringdiNEW ringdi
 4-Nov-12 ringideuNEW ringideu
 4-Nov-12 ringassNEW ringass
 4-Nov-12 ringclNEW ringcl
 4-Nov-12 ringiNEW  ringi
 4-Nov-12 isringNEW isring
 4-Nov-12 cnaddablNEW cnaddabl
 4-Nov-12 ablcomNEW ablcom
 4-Nov-12 ablgrpNEW ablgrp
 4-Nov-12 isabliNEW isabli
 4-Nov-12 isablNEW  isabl
 4-Nov-12 grplcanNEW grplcan
 4-Nov-12 grpinvidNEW grpinvid
 4-Nov-12 grpinvid2NEW grpinvid2
 4-Nov-12 grpinvid1NEW grpinvid1
 4-Nov-12 grprinvNEW grprinv
 4-Nov-12 grplinvNEW grplinv
 4-Nov-12 grpinvNEW grpinv
 4-Nov-12 grpinvclNEW grpinvcl
 4-Nov-12 grpinvvalNEW grpinvval
 4-Nov-12 grpinvfvalNEW grpinvfval
 4-Nov-12 grpidNEW  grpid
 4-Nov-12 grpinveuNEW grpinveu
 4-Nov-12 grprcanNEW grprcan
 4-Nov-12 grpridNEW grprid
 4-Nov-12 grplidNEW grplid
 4-Nov-12 grpidinv2NEW grpidinv2
 4-Nov-12 grpidclNEW grpidcl
 4-Nov-12 grpidvalNEW grpidval
 4-Nov-12 isgrpiNEW isgrpi
 4-Nov-12 grpn0NEW  grpn0
 4-Nov-12 grpideuNEW grpideu
 4-Nov-12 grpidinvNEW grpidinv
 4-Nov-12 grpidinvlem4NEW grpidinvlem4
 4-Nov-12 grpidinvlem3NEW grpidinvlem3
 4-Nov-12 grpidinvlem2NEW grpidinvlem2
 4-Nov-12 grpidinvlem1NEW grpidinvlem1
 4-Nov-12 grplidinvNEW grplidinv
 4-Nov-12 grpassNEW grpass
 4-Nov-12 grpclNEW  grpcl
 4-Nov-12 elgrpNEW  elgrp
 4-Nov-12 isgrp2NEW isgrp2
 4-Nov-12 isgrpNEW  isgrp
 4-Nov-12 df-ringNEW df-ring
 4-Nov-12 df-ablNEW df-abl
 4-Nov-12 df-grpNEW df-grp
 4-Nov-12 crgNEW    crg
 4-Nov-12 cabelNEW  cabel
 4-Nov-12 cgrpNEW   cgrp
 4-Nov-12 postr     posreltr
 4-Nov-12 isdivrng  isdivrngo
 4-Nov-12 df-drng   df-drngo
 4-Nov-12 ringrz    ringorz
 4-Nov-12 ringlz    ringolz
 4-Nov-12 ringridm  ringoridm
 4-Nov-12 ringlidm  ringolidm
 4-Nov-12 ringidmlem ringoidmlem
 4-Nov-12 ringgrp   ringogrpo
 4-Nov-12 ringabl   ringoablo
 4-Nov-12 ringdir   ringodir
 4-Nov-12 ringdi    ringodi
 4-Nov-12 ringideu  ringoideu
 4-Nov-12 ringass   ringoass
 4-Nov-12 ringcl    ringocl
 4-Nov-12 ringi     ringoi
 4-Nov-12 isring    isringo
 4-Nov-12 cnaddabl  cnaddablo
 4-Nov-12 ablcom    ablocom
 4-Nov-12 ablgrp    ablogrpo
 4-Nov-12 isabli    isabloi
 4-Nov-12 isabl     isablo
 4-Nov-12 grplcan   grpolcan
 4-Nov-12 grpinvid  grpoinvid
 4-Nov-12 grpinvid2 grpoinvid2
 4-Nov-12 grpinvid1 grpoinvid1
 4-Nov-12 grprinv   grporinv
 4-Nov-12 grplinv   grpolinv
 4-Nov-12 grpinv    grpoinv
 4-Nov-12 grpinvcl  grpoinvcl
 4-Nov-12 grpinvval grpoinvval
 4-Nov-12 grpinvfval grpoinvfval
 4-Nov-12 grpid     grpoid
 4-Nov-12 grpinveu  grpoinveu
 4-Nov-12 grprcan   grporcan
 4-Nov-12 grprid    grporid
 4-Nov-12 grplid    grpolid
 4-Nov-12 grpidinv2 grpoidinv2
 4-Nov-12 grpidcl   grpoidcl
 4-Nov-12 grpidval  grpoidval
 4-Nov-12 isgrpi    isgrpoi
 4-Nov-12 grpn0     grpon0
 4-Nov-12 grpideu   grpoideu
 4-Nov-12 grpidinv  grpoidinv
 4-Nov-12 grpidinvlem4 grpoidinvlem4
 4-Nov-12 grpidinvlem3 grpoidinvlem3
 4-Nov-12 grpidinvlem2 grpoidinvlem2
 4-Nov-12 grpidinvlem1 grpoidinvlem1
 4-Nov-12 grplidinv grpolidinv
 4-Nov-12 grpass    grpoass
 4-Nov-12 grpcl     grpocl
 4-Nov-12 isgrp2    isgrpo2
 4-Nov-12 isgrp     isgrpo
 4-Nov-12 df-ring   df-ringo
 4-Nov-12 df-abl    df-ablo
 4-Nov-12 df-grp    df-grpo
 4-Nov-12 1r        1sr
29-Oct-12 ralimdvaa ralimdva
28-Oct-12 mptfn     mptfng
26-Oct-12 raleqi    [--same--]  moved from PC's mathbox to main set.mm
26-Oct-12 fneq12d   [--same--]  moved from PC's mathbox to main set.mm
26-Oct-12 feq23i    [--same--]  moved from PC's mathbox to main set.mm
26-Oct-12 reseq2i   [--same--]  moved from PC's mathbox to main set.mm
26-Oct-12 reseq2d   [--same--]  moved from PC's mathbox to main set.mm
26-Oct-12 ifbieq2d  [--same--]  moved from PC's mathbox to main set.mm
26-Oct-12 supeq1d   [--same--]  moved from PC's mathbox to main set.mm
26-Oct-12 supeq1i   [--same--]  moved from PC's mathbox to main set.mm
26-Oct-12 emfin     0fin        moved from PC's mathbox to main set.mm
26-Oct-12 fz1n      [--same--]  moved from PC's mathbox to main set.mm
26-Oct-12 nn0lt10b  [--same--]  moved from PC's mathbox to main set.mm
25-Oct-12 fnoprab2ga [--same--]  moved from FL's mathbox to main set.mm
25-Oct-12 fnoprab2a [--same--]  moved from FL's mathbox to main set.mm
25-Oct-12 dmoprab2a [--same--]  moved from FL's mathbox to main set.mm
25-Oct-12 foprab2a  [--same--]  moved from FL's mathbox to main set.mm
25-Oct-12 oprabval2ga [--same--]  moved from FL's mathbox to main set.mm
25-Oct-12 oprabex2ga [--same--]  moved from FL's mathbox to main set.mm
22-Oct-12 ---       ---         math token "Bases" was changed to "TopBases"
21-Oct-12 stoi      [--same--]  converted to new structure scheme
21-Oct-12 topgele   [--same--]  converted to new structure scheme
21-Oct-12 subtopsin2 [--same--] converted to new structure scheme
21-Oct-12 topindis  [--same--]  converted to new structure scheme
21-Oct-12 stoig3    [--same--]  converted to new structure scheme
21-Oct-12 stoig2    [--same--]  converted to new structure scheme
21-Oct-12 stoig     [--same--]  converted to new structure scheme
21-Oct-12 stoiglem  [--same--]  converted to new structure scheme
20-Oct-12 retps     [--same--]  converted to new structure scheme
20-Oct-12 distps    [--same--]  converted to new structure scheme
20-Oct-12 indistps  [--same--]  converted to new structure scheme
20-Oct-12 istps5    [--same--]  converted to new structure scheme
20-Oct-12 istps4    [--same--]  converted to new structure scheme
20-Oct-12 istps3    [--same--]  converted to new structure scheme
20-Oct-12 istps2    [--same--]  converted to new structure scheme
20-Oct-12 istps     [--same--]  converted to new structure scheme
20-Oct-12 tpsex     ---         obsolete
20-Oct-12 istps     [--same--]  converted to new structure scheme
20-Oct-12 df-topsp  [--same--]  converted to new structure scheme
20-Oct-12 subsp2    subsp       moved from FL's mathbox to main set.mm
20-Oct-12 subsp     subspi
19-Oct-12 mpteqi    [--same--]  moved from SF's mathbox to main set.mm
19-Oct-12 mpteq2dva  [--same--]  moved from FL's mathbox to main set.mm
19-Oct-12 empntop   0ntop       moved from FL's mathbox to main set.mm
19-Oct-12 mp4an     [--same--]  moved from JM's mathbox to main set.mm
18-Oct-12 df-struct ---         obsolete; affected theorems reproved
18-Oct-12 df-strbldr ---        obsolete; affected theorems reproved
15-Oct-12 cbviin    [--same--]  moved from JGH's mathbox to main set.mm
15-Oct-12 cbviinv   [--same--]  moved from JGH's mathbox to main set.mm
15-Oct-12 txtopi    [--same--]  moved from JM's mathbox to main set.mm
15-Oct-12 txunii    [--same--]  moved from JM's mathbox to main set.mm
15-Oct-12 euuni2    [--same--]  moved from JM's mathbox to main set.mm
15-Oct-12 difxp     [--same--]  moved from JM's mathbox to main set.mm
15-Oct-12 unopn     [--same--]  moved from JM's mathbox to main set.mm
15-Oct-12 incld     [--same--]  moved from JM's mathbox to main set.mm
15-Oct-12 txopn     [--same--]  moved from JM's mathbox to main set.mm
15-Oct-12 txcld     [--same--]  moved from JM's mathbox to main set.mm
15-Oct-12 opnnei    [--same--]  moved from JGH's mathbox to main set.mm
 7-Oct-12 3ioran    [--same--]  moved from SF's mathbox to main set.mm
27-Aug-12 in23      in32
21-Jul-12 simplim   [--same--]  unnecessary negation removed
20-Jul-12 ---       ---         math token "base" was changed to "Base"
25-Jun-12 nelne     nelne1
24-Jun-12 an23      an32
22-Mar-12 simplld   simpld
21-May-12 fiss      [--same--]  moved from JGH's mathbox to main set.mm
21-May-12 inficlALT [--same--]  moved from JGH's mathbox to main set.mm
21-May-12 fitop     [--same--]  moved from JGH's mathbox to main set.mm
21-May-12 abrexex2g [--same--]  moved from JM's mathbox to main set.mm
16-Apr-12 rexcom4a  [--same--]  moved from JM's mathbox to main set.mm
16-Apr-12 rexcom4b  [--same--]  moved from JM's mathbox to main set.mm
16-Apr-12 eqfnfv3   [--same--]  moved from JM's mathbox to main set.mm
16-Apr-12 fibas     [--same--]  moved from JGH's mathbox to main set.mm
16-Apr-12 indexfi   [--same--]  moved from JM's mathbox to main set.mm
16-Apr-12 fipreima  [--same--]  moved from JM's mathbox to main set.mm
14-Apr-12 int2rel   brin
12-Apr-12 dif2rel   brdif       moved from SF's mathbox to main set.mm
25-Mar-12 syl3an2c  syl13anc    old hypothesis 1 is now hypothesis 5
25-Mar-12 syl3anc   syl111anc   old hypothesis 1 is now hypothesis 4
22-Mar-12 sylc      [--same--]  old hypothesis 1 is now hypothesis 4
22-Mar-12 sylanc    syl11anc    old hypothesis 1 is now hypothesis 4
22-Mar-12 syl2anr   syl22anc    old hypothesis 1 is now hypothesis 5
22-Mar-12 sylan31c  syl21anc    order of variables is different
22-Mar-12 sylan32c  syl12anc    order of variables is different
22-Mar-12 pm3.26im  simplim
22-Mar-12 pm3.27im  simprim
22-Mar-12 pm3.26    simpl
22-Mar-12 pm3.26i   simpli
22-Mar-12 pm3.26d   simpld
22-Mar-12 pm3.26bi  simplbi
22-Mar-12 pm3.27    simpr
22-Mar-12 pm3.27i   simpri
22-Mar-12 pm3.27d   simprd
22-Mar-12 pm3.27bi  simprbi
22-Mar-12 pm3.26bda simprbda
22-Mar-12 pm3.27bda simplbda
22-Mar-12 pm3.26bi2 simplbi2
22-Mar-12 pm3.26bi2VD simplbi2VD
22-Mar-12 3simp1    simp1
22-Mar-12 3simp2    simp2
22-Mar-12 3simp3    simp3
22-Mar-12 3simpl1   simpl1
22-Mar-12 3simpl2   simpl2
22-Mar-12 3simpl3   simpl3
22-Mar-12 3simpr1   simpr1
22-Mar-12 3simpr2   simpr2
22-Mar-12 3simpr3   simpr3
22-Mar-12 3simp1i   simp1i
22-Mar-12 3simp2i   simp2i
22-Mar-12 3simp3i   simp3i
22-Mar-12 3simp1d   simp1d
22-Mar-12 3simp2d   simp2d
22-Mar-12 3simp3d   simp3d
22-Mar-12 3simp1bi  simp1bi
22-Mar-12 3simp2bi  simp2bi
22-Mar-12 3simp3bi  simp3bi
22-Mar-12 3simp1l   simp1l
22-Mar-12 3simp1r   simp1r
22-Mar-12 3simp2l   simp2l
22-Mar-12 3simp2r   simp2r
22-Mar-12 3simp3l   simp3l
22-Mar-12 3simp3r   simp3r
22-Mar-12 3simp11   simp11
22-Mar-12 3simp12   simp12
22-Mar-12 3simp13   simp13
22-Mar-12 3simp21   simp21
22-Mar-12 3simp22   simp22
22-Mar-12 3simp23   simp23
22-Mar-12 3simp31   simp31
22-Mar-12 3simp32   simp32
22-Mar-12 3simp33   simp33
20-Mar-12 truni     [--same--]  moved from SF's mathbox to main set.mm
20-Mar-12 trsuc2    [--same--]  moved from SF's mathbox to main set.mm
20-Mar-12 trint     [--same--]  moved from SF's mathbox to main set.mm
20-Mar-12 trintss   [--same--]  moved from SF's mathbox to main set.mm
 4-Mar-12 ralunb    [--same--]  moved from SF's mathbox to main set.mm
20-Feb-12 3orcomb   [--same--]  moved from SF's mathbox to main set.mm
29-Jan-12 sbmo      [--same--]  moved from JM's mathbox to main set.mm
29-Jan-12 2ralor    [--same--]  moved from JM's mathbox to main set.mm
29-Jan-12 rexun     [--same--]  moved from JM's mathbox to main set.mm
29-Jan-12 ralun     [--same--]  moved from JM's mathbox to main set.mm
29-Jan-12 rexsn     [--same--]  moved from JM's mathbox to main set.mm
16-Jan-12 reuuninegi reuunineg
16-Jan-12 riotaund  riotaundb
 3-Jan-12 ee111     syl3c       moved from AS's mathbox to main set.mm
 3-Jan-12 ee12      sylsyld     moved from AS's mathbox to main set.mm
 3-Jan-12 ee20      syl6mpi     moved from AS's mathbox to main set.mm
22-Nov-11 eqfnfv3   [--same--]  moved from JM's mathbox to main set.mm
 6-Nov-11 cm        cmap
 4-Nov-11 hashgf1o  [--same--]  moved from PC's mathbox to main set.mm
 4-Nov-11 hashgval  [--same--]  moved from PC's mathbox to main set.mm
 4-Nov-11 hashginv  [--same--]  moved from PC's mathbox to main set.mm
 4-Nov-11 hashfz1   [--same--]  moved from PC's mathbox to main set.mm
 4-Nov-11 hashen    [--same--]  moved from PC's mathbox to main set.mm
 4-Nov-11 fz1fi     [--same--]  moved from PC's mathbox to main set.mm
20-Oct-11 ralab     [--same--]  moved from JM's mathbox to main set.mm
20-Oct-11 ralrab    [--same--]  moved from JM's mathbox to main set.mm
20-Sep-11 ifbieq2i  [--same--]  moved from PC's mathbox to main set.mm
20-Sep-11 dfiin2g   [--same--]  moved from JGH's mathbox to main set.mm
20-Sep-11 oprvex    ab2rexex    generalized oper. value to be arbitrary class
16-Sep-11 riotass2  reiotass2
16-Sep-11 riota2    reiota2
16-Sep-11 riota2f   reiota2f
16-Sep-11 riota1    reiota1
16-Sep-11 riotasbc    reiotasbc
16-Sep-11 riotacl   reiotacl
16-Sep-11 riotacl2  reiotacl2
15-Sep-11 19.22-2   2exim
15-Sep-11 19.20-2   2alim
15-Sep-11 19.20ii2  2al2imi
15-Sep-11 19.20ian2 2alanimi
15-Sep-11 sbc19.20dv sbcimdv
15-Sep-11 r19.22dva reximdva
15-Sep-11 r19.22sdv reximdv
15-Sep-11 r19.22dv  reximdvai
15-Sep-11 r19.22dv2 reximdv2
15-Sep-11 r19.22d   reximdai
15-Sep-11 r19.22si  reximi
15-Sep-11 r19.22i2  reximi2
15-Sep-11 r19.22i   reximia
15-Sep-11 r19.22OLD reximOLD
15-Sep-11 r19.22    rexim
15-Sep-11 r19.20dv2 ralimdv2
15-Sep-11 r19.20sdv ralimdv
15-Sep-11 r19.20dva ralimdva
15-Sep-11 r19.20da  ralimdaa
15-Sep-11 r19.20sii ral2imi
15-Sep-11 r19.20si  ralimi
15-Sep-11 r19.20ia  ralimiaa
15-Sep-11 r19.20i   ralimia
15-Sep-11 r19.20i2  ralimi2
15-Sep-11 r19.20    ralim
15-Sep-11 19.22dvv  2eximdv
15-Sep-11 19.20dvv  2alimdv
15-Sep-11 19.22dv   eximdv
15-Sep-11 19.20dv   alimdv
15-Sep-11 19.22d    eximd
15-Sep-11 19.22i2   2eximi
15-Sep-11 19.22i    eximi
15-Sep-11 19.22     exim
15-Sep-11 19.20d    alimd
15-Sep-11 19.20ian  alanimi
15-Sep-11 19.20ii   al2imi
15-Sep-11 19.20     alim
15-Sep-11 19.20i2   2alimi
15-Sep-11 19.20i    alimi
15-Sep-11 rexeqd    rexeqbi1dv
15-Sep-11 rexeq1d   rexeqdv
15-Sep-11 rexeq1    rexeq
15-Sep-11 rexeq1f   rexeqf
15-Sep-11 raleq1i   raleqi
15-Sep-11 raleqd    raleqbi1dv
15-Sep-11 raleq1d   raleqdv
15-Sep-11 raleq1    raleq
15-Sep-11 raleq1f   raleqf
15-Sep-11 rabeq12d  rabeqbidv   moved from JM's mathbox to main set.mm
15-Sep-11 19.18-2   2exbi
15-Sep-11 19.15-2   2albi
15-Sep-11 r19.15    ralbi
15-Sep-11 19.18     exbi
15-Sep-11 19.15     albi
15-Sep-11 2albi     2albiim
15-Sep-11 albi      albiim
14-Sep-11 ciota     cio
14-Sep-11 rabbii    rabbiia
14-Sep-11 rabbisdv  rabbidv
14-Sep-11 rabbidv   rabbidva
14-Sep-11 tpi3      tpid3
14-Sep-11 tpi2      tpid2
14-Sep-11 tpi1      tpid1
13-Sep-11 dmfnwdm2  fnprgOLD       moved from FL's mathbox to main set.mm
13-Sep-11 s2pf      funprgOLD      moved from FL's mathbox to main set.mm
12-Sep-11 mptexg    [--same--]  swapped variables "B" and "C"
 9-Sep-11 hbcmpt    hbmpt1      moved from FL's mathbox to main set.mm
 9-Sep-11 bnj1344   simp3bi    moved from JBN's mathbox to main set.mm
 9-Sep-11 bnj1301   simp2bi    moved from JBN's mathbox to main set.mm
 9-Sep-11 bnj1206   simp1bi    moved from JBN's mathbox to main set.mm
 8-Sep-11 syl3an2c  [--same--]  moved from JM's mathbox to main set.mm
 8-Sep-11 eqfnfvALT eqfnfv2
 8-Sep-11 uridm2    ringoridm
 8-Sep-11 uridm1    ringolidm
 8-Sep-11 uridm     ringoidmlem
 8-Sep-11 zerab2    ringorz
 8-Sep-11 zerab     ringolz
 7-Sep-11 euunian   iota4an     moved from ATS's mathbox to main set.mm
 7-Sep-11 iota3     iota4       (because it's analogous to reuunisbc / riota4)
 6-Sep-11 pm13.181  [--same--]  moved from ATS's mathbox to main set.mm
 6-Sep-11 pm13.18   [--same--]  moved from ATS's mathbox to main set.mm
 6-Sep-11 trutru    tru         moved from AH's mathbox to main set.mm
 6-Sep-11 nofaltru  notfal      moved from AH's mathbox to main set.mm
 4-Sep-11 feq1i     [--same--]  moved from PC's mathbox to main set.mm
 4-Sep-11 fneq1i    [--same--]  moved from PC's mathbox to main set.mm
 4-Sep-11 fneq2d    [--same--]  moved from PC's mathbox to main set.mm
 4-Sep-11 fneq1d    [--same--]  moved from PC's mathbox to main set.mm
 3-Sep-11 prf       fpr         moved from JM's mathbox to main set.mm
 3-Sep-11 prfv2     fvpr2       moved from JM's mathbox to main set.mm
 3-Sep-11 prfv1     fvpr1       moved from JM's mathbox to main set.mm
 3-Sep-11 prfun     funpr       moved from JM's mathbox to main set.mm
30-Aug-11 eqfnfvf2  eqfnfv2f
30-Aug-11 xp11a     xpcan2      xp11a (obsolete) was a special case of xpcan2
30-Aug-11 xp11b     xpcan       xp11b (obsolete) was a special case of xpcan
26-Aug-11 dmsdtriord domtriord  moved from JGH's mathbox to main set.mm
26-Aug-11 impbid3   impcon4bid  moved from JGH's mathbox to main set.mm
26-Aug-11 cbvcsb    [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 cbvcsb    [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 ordiso    [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 ordtypelem1 [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 ordtypelem2 [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 ordtypelem3 [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 ordtypelem4 [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 ordtypelem5 [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 ordtypelem6 [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 ordtypelem7 [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 ordtype   [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 hartoglem [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 hartog    [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 onsdom    [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 omsubsuc  [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 omsubsuc2 [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 omsubsdomlem1 [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 omsubsdomlem2 [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 omsubsdom [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 omsubdom  [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 omsubel   [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 omsubss   [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 elomsubsd [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 omsubdmss [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 omsublim  [--same--]  moved from JGH's mathbox to main set.mm
26-Aug-11 omsubindss [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 infenomsub [--same--] moved from JGH's mathbox to main set.mm
26-Aug-11 omsubinit [--same--]  moved from JGH's mathbox to main set.mm
20-Aug-11 iotaval   [--same--]  swapped order of equality in consequent
20-Aug-11 iotaequ   [--same--]  swapped order of equality in consequent
20-Aug-11 iotanul   [--same--]  swapped order of equality
18-Aug-11 mpset     mptexg      moved from FL's mathbox to main set.mm
18-Aug-11 hbiota    hbiota1     moved from ATS's mathbox to main set.mm
18-Aug-11 iotacl    [--same--]  moved from ATS's mathbox to main set.mm
18-Aug-11 iota3     [--same--]  moved from ATS's mathbox to main set.mm
18-Aug-11 iotaex    [--same--]  moved from ATS's mathbox to main set.mm
18-Aug-11 iotanul   [--same--]  moved from ATS's mathbox to main set.mm
18-Aug-11 iotaequ   [--same--]  moved from ATS's mathbox to main set.mm
18-Aug-11 iotaval   [--same--]  moved from ATS's mathbox to main set.mm
18-Aug-11 sbeqalb   [--same--]  moved from ATS's mathbox to main set.mm
18-Aug-11 sbceqal   [--same--]  moved from ATS's mathbox to main set.mm
18-Aug-11 eqsbc3    [--same--]  moved from ATS's mathbox to main set.mm
18-Aug-11 19.20ian  [--same--]  moved from ATS's mathbox to main set.mm
17-Aug-11 mpt2g     ovmpt2g
17-Aug-11 mptg      fvmptg
17-Aug-11 bnj1226   imorri      moved from JBN's mathbox to main set.mm
17-Aug-11 jad       [--same--]  moved from SF's mathbox to main set.mm
13-Aug-11 ceqsex3v  ---         (RM's mathbox) - obsolete; use ceqsexgv
13-Aug-11 ceqsex3   ---         (RM's mathbox) - obsolete; use ceqsexg
13-Aug-11 ceqsex2v  [--same--]  reformatted to use triple conjunction
13-Aug-11 ceqsex2   [--same--]  reformatted to use triple conjunction
 9-Aug-11 feq2d     [--same--]  moved from PC's mathbox to main set.mm
 9-Aug-11 bnj1456   snssd       moved from JBN's mathbox to main set.mm
 9-Aug-11 snssd     [--same--]  moved from JGH's mathbox to main set.mm
 9-Aug-11 fbaslim   [--same--]  moved from JGH's mathbox to main set.mm
 9-Aug-11 fbfgss    [--same--]  moved from JGH's mathbox to main set.mm
 9-Aug-11 fgid      [--same--]  moved from JGH's mathbox to main set.mm
 9-Aug-11 cnpnei    [--same--]  moved from JGH's mathbox to main set.mm
 9-Aug-11 limfilss  [--same--]  moved from JGH's mathbox to main set.mm
 9-Aug-11 fbfgfmeq  [--same--]  moved from JGH's mathbox to main set.mm
 9-Aug-11 fgss      [--same--]  moved from JGH's mathbox to main set.mm
 9-Aug-11 filmapss  [--same--]  moved from JGH's mathbox to main set.mm
18-Jul-11 ompfl3    3anibar
18-Jul-11 rexeq12d  rexeqbidv
18-Jul-11 raleq12d  raleqbidv
18-Jul-11 ralbieq1dv ---        obsolete; use raleqbidv
18-Jul-11 exan2     exsimpl
 8-Jul-11 brab1     [--same--]  changed set var "y" to class var "A"
29-Jun-11 exan2     [--same--]  moved from RM's mathbox to main set.mm
29-Jun-11 wfal      [--same--]  moved from AH's mathbox to main set.mm
29-Jun-11 df-fal    [--same--]  moved from AH's mathbox to main set.mm
29-Jun-11 wtru      [--same--]  moved from AH's mathbox to main set.mm
29-Jun-11 df-tru    [--same--]  moved from AH's mathbox to main set.mm
29-Jun-11 mptfn     [--same--]  moved from SF's mathbox to main set.mm
29-Jun-11 rnmpt     [--same--]  moved from SF's mathbox to main set.mm
29-Jun-11 dford2    [--same--]  moved from SF's mathbox to main set.mm
29-Jun-11 funsngxx  funsngOLD      changed "e. _V" to "e. C", "e. D" in antec.
29-Jun-11 bnj94     funsngxx    moved from JBN's mathbox to main set.mm
29-Jun-11 bnj928    fnsnOLD        moved from JBN's mathbox to main set.mm
29-Jun-11 bnj1257   eleq2s      moved from JBN's mathbox to main set.mm
29-Jun-11 bnj1495   funeqi      moved from JBN's mathbox to main set.mm
29-Jun-11 erdisj2   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 cass      [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 df-ass    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 isass     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 isexid    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 ismgm     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 opidon    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 rngopid   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 opidon2   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 isexid2   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 exidu1    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 idrval    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 iorlid    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 cmpidelt  [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 csem      [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 df-sgr    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 smgrpismgm [--same--] moved from FL's mathbox to main set.mm
29-Jun-11 issmgrp   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 smgrpmgm  [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 smgrpass  [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 cmnd      [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 df-mnd    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 mndissmgrp [--same--] moved from FL's mathbox to main set.mm
29-Jun-11 mndisexid [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 mndismgm  [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 mndmgmid  [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 ismnd     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 ismnd1    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 relrng    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 rngn0     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 rngmgmbs4 [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 rnplrnml0 [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 rnplrnml2 [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 rnplrnml  [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 unmnd     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 fora1     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 fora2     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 fora      [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 uridm     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 uridm1    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 zerab     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 zerab2    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 on1el3    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 on1el4    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 on1el6    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 ring1cl   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 uznzr     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 isdivrngo  [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 zrdivrng  [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 dvrunz    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 clmgm     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 uridm2    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 grpmnd    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 iscom2    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 ismnd2    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 difeq12   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 setwoe    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 sfseqeq   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 opreq123d [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 oprabvaligg [--same--] moved from FL's mathbox to main set.mm
29-Jun-11 cexid     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 df-exid   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 cmagm     [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 df-mgm    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 ccm2      [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 df-com2   [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 cfld      [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 df-fld    [--same--]  moved from FL's mathbox to main set.mm
29-Jun-11 imp5a     [--same--]  moved from JGH's mathbox to main set.mm
29-Jun-11 iccleub   [--same--]  moved from JGH's mathbox to main set.mm
29-Jun-11 expl      [--same--]  moved from JGH's mathbox to main set.mm
29-Jun-11 ghomid    [--same--]  moved from PC's mathbox to main set.mm
29-Jun-11 ghomlin   [--same--]  moved from PC's mathbox to main set.mm
28-Jun-11 infmssuzle [--same--] removed redundant antecedent S =/= (/)
22-Jun-11 xpeq12    [--same--]  moved from FL's mathbox to main set.mm
22-Jun-11 xpeq12i   [--same--]  moved from FL's mathbox to main set.mm
21-Jun-11 axnul2    axnulALT
25-Mar-11 ntunte    inuni
 8-Mar-11 ssxp      xpss12
 8-Mar-11 bepart    elelpwi
 8-Mar-11 intprd    intprg      changed "e. _V" to "e. C", "e. D" in antec.
 2-Mar-11 equnamo   n0moeu
21-Feb-11 muln0b    mulne0b
21-Feb-11 muln0i    mulne0i
16-Jan-11 grothinf  grothomex
13-Jan-11 hbequid   hbequid2
10-Dec-10 nexnoti   nexr
31-Oct-10 reu3xxx   reu6
31-Oct-10 reu6      reu3
31-Oct-10 reu3      reu3xxx
30-Oct-10 eusn      euabsn
26-Oct-10 raaan     raaanv
18-Oct-10 ---       ---         changed math symbol from "C=" to "C_"
 3-Oct-10 ---       ---         added variables E, e, I, i, V
 3-Oct-10 ---       ---         changed math symbol from "P~" to "~P"
 3-Oct-10 ---       ---         changed math symbol from "H~" to "~H"
 3-Oct-10 ---       ---         changed math symbol from "(_" to "C="
 3-Oct-10 ---       ---         changed math symbol from "(." to "C."
 3-Oct-10 ---       ---         changed math symbol from "C." to "_C"
 3-Oct-10 ---       ---         changed math symbol from "E" to "_E"
 3-Oct-10 ---       ---         changed math symbol from "e" to "_e"
 3-Oct-10 ---       ---         changed math symbol from "I" to "_I"
 3-Oct-10 ---       ---         changed math symbol from "i" to "_i"
 3-Oct-10 ---       ---         changed math symbol from "V" to "_V"
24-Jul-09 sandbox   mathbox
12-Jun-09 mulge0    [--same--]  rearranged antecedent
12-Jun-09 mulgt0    [--same--]  rearranged antecedent
12-May-09 ---       ---         changed math symbol from "ZZ_>" to "ZZ>="
 2-May-09 snsspr    snsspr1
 2-May-09 axpow     zfpow
 2-May-09 axac      zfac
 2-May-09 axun      zfun
27-Apr-09 pm4.22    bitr
24-Apr-09 axinf     zfinf
24-Apr-09 zfinf     zfinf2
 2-Apr-09 infmssuzle [--same--] changed -. S = (/) to S =/= (/)
23-Mar-09 eqfnfvf   ---         obsolete; use eqfnfvf2 instead
23-Mar-09 ffnoprval ffnoprv
23-Mar-09 eqfnoprval eqfnoprv
23-Mar-09 fnoprval  fnoprv
23-Mar-09 foprval   foprv
23-Mar-09 oprvalres oprvres
23-Mar-09 oprssoprval oprssoprv
23-Mar-09 fnrnoprval fnrnoprv
23-Mar-09 fooprval  fooprv
23-Mar-09 fnoprvalrn fnoprvrn
23-Mar-09 oprvalelrn oprvelrn
23-Mar-09 oprvalconst2 oprvconst2
23-Mar-09 oprvalex  oprvex
23-Mar-09 symgoprval symgoprv
23-Mar-09 fnoprvalrn2 fnoprvrn2
22-Mar-09 icoshf    icoshft
 8-Mar-09 nnont     nnon
 7-Mar-09 eluzsubii eluzsubi
 7-Mar-09 eluzaddii eluzaddi
 7-Mar-09 divexp    expdiv
 7-Mar-09 recexp    exprec
 7-Mar-09 ---       ---         changed math symbol from "ZZ>" to "ZZ_>"
27-Feb-09 lediv23   [--same--]  rearranged antecedent
27-Feb-09 ltdiv23   [--same--]  rearranged antecedent
 3-Jan-09 muln0     mulne0
 3-Jan-09 vne0      vn0
 3-Jan-09 n0        neq0
 3-Jan-09 ne0       n0
 3-Jan-09 ssne0     ssn0
 3-Jan-09 onne0     onn0
 3-Jan-09 dmsnne0   dmsnn0
 3-Jan-09 rnsnne0   rnsnn0
 3-Jan-09 1ne0      1n0
 3-Jan-09 metne0    metn0
 3-Jan-09 blne0     bln0
 2-Jan-08 flrecl    reflcl
30-Dec-08 letrdi    letrd
30-Dec-08 lelttrdi  lelttrd
30-Dec-08 ltletrdi  ltletrd
30-Dec-08 lttrdi    lttrd
29-Dec-08 hbnegi    hbneg
29-Dec-08 hbnegdi   hbnegd
29-Dec-08 hbsumi    hbsum
29-Dec-08 hbsum1i   hbsum1
28-Dec-08 negnei    negne0i
28-Dec-08 negne0i   negne0bi
28-Dec-08 lemul2    [--same--]  rearranged antecedent
28-Dec-08 lemul1    [--same--]  rearranged antecedent
28-Dec-08 ltmul2    [--same--]  rearranged antecedent
28-Dec-08 ltmul1    [--same--]  rearranged antecedent
28-Dec-08 ecdmn0    [--same--]  changed -. ... = to =/=
27-Dec-08 divdiv24  [--same--]  rearranged antecedent
27-Dec-08 divdiv13  [--same--]  rearranged antecedent
27-Dec-08 divadddiv [--same--]  rearranged antecedent
27-Dec-08 divdivdiv [--same--]  rearranged antecedent
27-Dec-08 recndi    recnd
27-Dec-08 divdivmul divdiv1
27-Dec-08 divdiv23  [--same--]  rearranged antecedent
27-Dec-08 dmsnsn0   ---         obsolete; use the more general dmsn0el
25-Dec-08 div12     [--same--]  rearranged antecedent
25-Dec-08 div13     [--same--]  rearranged antecedent
25-Dec-08 div23     [--same--]  rearranged antecedent
25-Dec-08 expm1     expm1t
25-Dec-08 divmuldiv [--same--]  rearranged antecedent
25-Dec-08 recexp    [--same--]  rearranged antecedent
25-Dec-08 expne0i   [--same--]  rearranged antecedent
25-Dec-08 expsub    [--same--]  rearranged antecedent
25-Dec-08 divexp    [--same--]  rearranged antecedent
21-Dec-08 imaun2    imaundir
21-Dec-08 imaun     imaundi
19-Dec-08 sbhyp     ---         obsolete; use sbhypf
19-Dec-08 opelcog   opelco2g
18-Dec-08 fsumspl   fsumsplit
18-Dec-08 fsum0spl  fsum0split
18-Dec-08 fsumshf   fsumshft
18-Dec-08 fsumcons  fsumconst
18-Dec-08 dmco2     dmco
17-Dec-08 ---       ---         the math token "Base" was changed to "BaseSet"
17-Dec-08 ssxpr     ---         obsolete; use ssxpb
17-Dec-08 nicodraw  ---         obsolete; use nic-ax
17-Dec-08 nicodmpraw ---        obsolete; use nic-mp
17-Dec-08 3exbi     3exbii
17-Dec-08 relssdr   relssdmrn
16-Dec-08 dfoprab4  dfoprab5s
16-Dec-08 dfoprab5  dfoprab4s
16-Dec-08 dffxxx    dff2
16-Dec-08 dff4      dff3
16-Dec-08 dff3      dff4
16-Dec-08 dff4      dffxxx
16-Dec-08 dffunmo   dffun6
16-Dec-08 dffun6    dffun7
16-Dec-08 dffun7    dffun8
16-Dec-08 dffun8    dffun9
16-Dec-08 dffunmof  dffun6f
16-Dec-08 fnopabfv  dffn5
16-Dec-08 fnforn    dffn4
16-Dec-08 fnfrn     dffn3
16-Dec-08 fnf       dffn2
16-Dec-08 f1fvf     dff13f
16-Dec-08 f1fv      dff13
16-Dec-08 f11       dff12
16-Dec-08 f1ofv     dff1o6
16-Dec-08 f1o5      dff1o5
16-Dec-08 f1o4      dff1o4
16-Dec-08 f1o3      dff1o3
16-Dec-08 f1o2      dff1o2
15-Dec-08 pm4.2d    biidd
15-Dec-08 pm4.2     biid
15-Dec-08 pm4.1     con34b
15-Dec-08 bi2.15    con1b
15-Dec-08 bi2.03    con2b
15-Dec-08 a3d       con4d
15-Dec-08 a3i       con4i
13-Dec-08 2climnni  2climnn
13-Dec-08 2climnn0i 2climnn0
12-Dec-08 reeftlclti reeftlcl
12-Dec-08 eftlclti  eftlcl
12-Dec-08 eftlexti  eftlex
12-Dec-08 fnsmnti   arisumi
12-Dec-08 nn0le2msqti nn0le2msqi
12-Dec-08 reccnvi   reccnv
12-Dec-08 expcnvi   expcnv
11-Dec-08 isummulc1i isummulc1
11-Dec-08 iserzgt0i iserzgt0
11-Dec-08 isumreclti isumrecl
11-Dec-08 isumclti  isumcl
11-Dec-08 isumnn0nni isumnn0nn
11-Dec-08 isum1pi   isum1p
11-Dec-08 isumnuli  isumnul
11-Dec-08 isumclim5ti isumclim5
11-Dec-08 isumclim4ti isumclim4
11-Dec-08 isumclim3ti isumclim3
11-Dec-08 isumclim2ti isumclim2
11-Dec-08 isumclim2tfi isumclim2f
11-Dec-08 isum1climi isum1clim
11-Dec-08 isumclimti isumclim
11-Dec-08 isumval2ti isumval2
11-Dec-08 isumvalti isumval
11-Dec-08 cvgcmp3ceti cvgcmp3ce
11-Dec-08 iserzcmp0i iserzcmp0
11-Dec-08 iserzcmpi iserzcmp
11-Dec-08 climsqueeze2i climsqueeze2
11-Dec-08 climsqueezei climsqueeze
11-Dec-08 climcmpc1i climcmpc1
11-Dec-08 climcmpi  climcmp
11-Dec-08 iserzmulc1i iserzmulc1
11-Dec-08 iserzexti iserzex
11-Dec-08 clim2serzti clim2serz
11-Dec-08 climsubc2i climsubc2
11-Dec-08 climsubi  climsub
11-Dec-08 climmulc2i climmulc2
11-Dec-08 climmuli  climmul
11-Dec-08 climaddc2i climaddc2
11-Dec-08 climaddc1i climaddc1
11-Dec-08 climaddi  climadd
11-Dec-08 climge0i  climge0
11-Dec-08 climrecli climrecl
11-Dec-08 climreui  climreu
11-Dec-08 climeui   climeu
11-Dec-08 climuniii climunii
11-Dec-08 climunii  climuni
11-Dec-08 clm4ati   clm4a
11-Dec-08 serzmulc1i serzmulc1
11-Dec-08 serzspliti serzsplit
11-Dec-08 serzcmp0i serzcmp0
11-Dec-08 serzcmpi  serzcmp
11-Dec-08 serz1pi   serz1p
11-Dec-08 serzreclti serzrecl
11-Dec-08 serzcl2ti serzcl2
11-Dec-08 ser1clti  ser1cl
11-Dec-08 ser0clti  ser0cl
11-Dec-08 serzclti  serzcl
11-Dec-08 fsum4i    fsum4
11-Dec-08 fsum3i    fsum3
11-Dec-08 fsum2i    fsum2
11-Dec-08 fsum0spli fsum0spl
11-Dec-08 fsumspli  fsumspl
11-Dec-08 serzfsumi serzfsum
11-Dec-08 fsumserz2i fsumserz2
11-Dec-08 fsumserzi fsumserz
11-Dec-08 cvg1ii    cvg1i
11-Dec-08 cvg1i     cvg1
11-Dec-08 seqzres2i seqzres2
11-Dec-08 seqzresi  seqzres
11-Dec-08 seqzresvali seqzresval
11-Dec-08 seqzcli   seqzcl
11-Dec-08 seqzrni   seqzrn
11-Dec-08 seqzrn2i  seqzrn2
11-Dec-08 seqzeqi   seqzeq
11-Dec-08 seqzfveqi seqzfveq
11-Dec-08 seqzval2ti seqzval2
11-Dec-08 seq01i    seq01
11-Dec-08 seq0p1i   seq0p1
11-Dec-08 seq00i    seq00
11-Dec-08 seqzm1i   seqzm1
11-Dec-08 seqzp1i   seqzp1
11-Dec-08 seqz1i    seqz1
11-Dec-08 seq0fni   seq0fn
11-Dec-08 seq1seq0i seq1seq0
11-Dec-08 seq1seq0ti seq1seq01
11-Dec-08 seq1seq02ti seq1seq02
11-Dec-08 seq0seqzi seq0seqz
11-Dec-08 seq1seqzi seq1seqz
11-Dec-08 seqzvalti seqzval
11-Dec-08 seqzfni   seqzfn
11-Dec-08 seqzfval2i seqzfval2
11-Dec-08 seqzfvali seqzfval
11-Dec-08 seq0valti seq0valt
11-Dec-08 seq0fvali seq0fval
11-Dec-08 seq1shftidi seq1shftid
11-Dec-08 shftidti  shftidt
11-Dec-08 shftcan1ti shftcan1
11-Dec-08 shftcan2ti shftcan2
11-Dec-08 shftfi    shftf
11-Dec-08 shftval5ti shftval5
11-Dec-08 shftval4ti shftval4
11-Dec-08 shftval3ti shftval3
11-Dec-08 shftval2ti shftval2
11-Dec-08 shftvalti shftval
11-Dec-08 shftresvalti shftresval
11-Dec-08 shftresi  shftres
11-Dec-08 shftfni   shftfn
11-Dec-08 shftfvali shftfval
11-Dec-08 seq1resi  seq1res
11-Dec-08 seq1cl2i  seq1cl2
11-Dec-08 seq1cli   seq1cl
11-Dec-08 seq1f2i   seq1f2
11-Dec-08 seq1fi    seq1f
11-Dec-08 seq1rni   seq1rn
11-Dec-08 seq1rn2i  seq1rn2
11-Dec-08 seq1fni   seq1fn
11-Dec-08 seq1m1i   seq1m1
11-Dec-08 seq1p1i   seq1p1
11-Dec-08 seq11i    seq11
11-Dec-08 seq1val2i seq1val2
11-Dec-08 seq1vali  seq1val
11-Dec-08 seq1rvali seq1rval
11-Dec-08 uznegi    uzneg
 9-Dec-08 nvelv     vprc
 9-Dec-08 inelv     iprc
 9-Dec-08 fipr      fiprc
 9-Dec-08 ecqs      [--same--]  eliminated redundant hypothesis A e. _V
18-Nov-08 ---       ---         See mmnotes.txt entry of 18-Nov-2008
18-Nov-08 cdavalt   cdaval
18-Nov-08 cdaval    cdavali
18-Nov-08 unbnnt    unbnn3
18-Nov-08 frsuct    frsuc
18-Nov-08 fr0t      fr0g
18-Nov-08 rdg0t     rdg0g
18-Nov-08 ssonunit  ssonuni
18-Nov-08 ssonuni   ssonunii
18-Nov-08 eqtr3t    eqtr3
18-Nov-08 eqtr2t    eqtr2
18-Nov-08 eqtrt     eqtr
18-Nov-08 3eqtr4r   3eqtr4ri
18-Nov-08 3eqtr3r   3eqtr3ri
18-Nov-08 3eqtr2r   3eqtr2ri
18-Nov-08 3eqtr4r   3eqtr4ri
18-Nov-08 3eqtr3r   3eqtr3ri
18-Nov-08 3bitr3r   3bitr3ri
18-Nov-08 3bitr4r   3bitr4ri
18-Nov-08 3bitr2r   3bitr2ri
18-Nov-08 biimpr    biimpri
18-Nov-08 biimp     biimpi
18-Nov-08 impbi     impbii
18-Nov-08 ---       ---         See mmnotes.txt entry of 17-Nov-2008
17-Nov-08 ---       ---         Remember that substitutions are
17-Nov-08 ---       ---         made in _reverse_ order.
17-Nov-08 efi4pt    efi4p
17-Nov-08 resin4pt  resin4p
17-Nov-08 recos4pt  recos4p
17-Nov-08 ef4pt     ef4p
17-Nov-08 addclt    addcl
17-Nov-08 readdclt  readdcl
17-Nov-08 mulclt    mulcl
17-Nov-08 remulclt  remulcl
17-Nov-08 addcomt   addcom
17-Nov-08 mulcomt   mulcom
17-Nov-08 addasst   addass
17-Nov-08 mulasst   mulass
17-Nov-08 adddit    adddi
17-Nov-08 addid1t   addid1
17-Nov-08 mulid1t   mulid1
17-Nov-08 recnt     recn
17-Nov-08 adddirt   adddir
17-Nov-08 addid2t   addid2
17-Nov-08 add12t    add12
17-Nov-08 add23t    add23
17-Nov-08 add4t     add4
17-Nov-08 add42t    add42
17-Nov-08 cnegext   cnegex
17-Nov-08 cnegextlem1 cnegexlem1
17-Nov-08 cnegextlem2 cnegexlem2
17-Nov-08 cnegextlem3 cnegexlem3
17-Nov-08 addcant   addcan
17-Nov-08 addcan2t  addcan2
17-Nov-08 subvalt   subval
17-Nov-08 subclt    subcl
17-Nov-08 negclt    negcl
17-Nov-08 subaddt   subadd
17-Nov-08 subsub23t subsub23
17-Nov-08 pncan3t   pncan3
17-Nov-08 negidt    negid
17-Nov-08 negsubt   negsub
17-Nov-08 addsubasst addsubass
17-Nov-08 addsubt   addsub
17-Nov-08 subadd23t subadd23
17-Nov-08 addsub12t addsub12
17-Nov-08 2addsubt  2addsub
17-Nov-08 negnegt   negneg
17-Nov-08 subnegt   subneg
17-Nov-08 subidt    subid
17-Nov-08 subid1t   subid1
17-Nov-08 pncant    pncan
17-Nov-08 pncan2t   pncan2
17-Nov-08 npcant    npcan
17-Nov-08 npncant   npncan
17-Nov-08 nppcant   nppcan
17-Nov-08 subcan2t  subcan2
17-Nov-08 subeq0t   subeq0
17-Nov-08 neg11t    neg11
17-Nov-08 negcon1t  negcon1
17-Nov-08 negcon2t  negcon2
17-Nov-08 subcant   subcan
17-Nov-08 mulid2t   mulid2
17-Nov-08 mul12t    mul12
17-Nov-08 mul23t    mul23
17-Nov-08 mul4t     mul4
17-Nov-08 muladdt   muladd
17-Nov-08 muladd11t muladd11
17-Nov-08 subdit    subdi
17-Nov-08 subdirt   subdir
17-Nov-08 renegclt  renegcl
17-Nov-08 resubclt  resubcl
17-Nov-08 mul01t    mul01
17-Nov-08 mul02t    mul02
17-Nov-08 mulneg1t  mulneg1
17-Nov-08 mulneg2t  mulneg2
17-Nov-08 mulneg12t mulneg12
17-Nov-08 mul2negt  mul2neg
17-Nov-08 negdit    negdi
17-Nov-08 negdi2t   negdi2
17-Nov-08 negsubdit negsubdi
17-Nov-08 negsubdi2t negsubdi2
17-Nov-08 neg2subt  neg2sub
17-Nov-08 submul2t  submul2
17-Nov-08 subsub2t  subsub2
17-Nov-08 subsubt   subsub
17-Nov-08 subsub3t  subsub3
17-Nov-08 subsub4t  subsub4
17-Nov-08 sub23t    sub23
17-Nov-08 nnncant   nnncan
17-Nov-08 nnncan1t  nnncan1
17-Nov-08 nnncan2t  nnncan2
17-Nov-08 nncant    nncan
17-Nov-08 nppcan2t  nppcan2
17-Nov-08 mulm1t    mulm1
17-Nov-08 addsub4t  addsub4
17-Nov-08 subadd4t  subadd4
17-Nov-08 sub4t     sub4
17-Nov-08 mulsubt   mulsub
17-Nov-08 pnpcant   pnpcan
17-Nov-08 pnpcan2t  pnpcan2
17-Nov-08 pnncant   pnncan
17-Nov-08 ppncant   ppncan
17-Nov-08 ltxrt     ltxr
17-Nov-08 rexrt     rexr
17-Nov-08 ltxrltt   ltxrlt
17-Nov-08 xrlenltt  xrlenlt
17-Nov-08 xrltnlet  xrltnle
17-Nov-08 lttrt     lttr
17-Nov-08 mulgt0t   mulgt0
17-Nov-08 lenltt    lenlt
17-Nov-08 ltnlet    ltnle
17-Nov-08 lttri2t   lttri2
17-Nov-08 lttri3t   lttri3
17-Nov-08 lttri4t   lttri4
17-Nov-08 ltnet     ltne
17-Nov-08 letri3t   letri3
17-Nov-08 leloet    leloe
17-Nov-08 eqleltt   eqlelt
17-Nov-08 ltlet     ltle
17-Nov-08 leltnet   leltne
17-Nov-08 ltlent    ltlen
17-Nov-08 lelttrt   lelttr
17-Nov-08 ltletrt   ltletr
17-Nov-08 letrt     letr
17-Nov-08 ltnrt     ltnr
17-Nov-08 leidt     leid
17-Nov-08 ltnsymt   ltnsym
17-Nov-08 ltnsym2t  ltnsym2
17-Nov-08 renepnft  renepnf
17-Nov-08 renemnft  renemnf
17-Nov-08 xrltnrt   xrltnr
17-Nov-08 ltpnft    ltpnf
17-Nov-08 mnfltt    mnflt
17-Nov-08 mnfltxrt  mnfltxr
17-Nov-08 pnfnltt   pnfnlt
17-Nov-08 nltmnft   nltmnf
17-Nov-08 pnfget    pnfge
17-Nov-08 mnflet    mnfle
17-Nov-08 xrltnsymt xrltnsym
17-Nov-08 xrltnsym2t xrltnsym2
17-Nov-08 xrlttrit  xrlttri
17-Nov-08 xrlttrt   xrlttr
17-Nov-08 xrlttri2t xrlttri2
17-Nov-08 xrlttri3t xrlttri3
17-Nov-08 xrleloet  xrleloe
17-Nov-08 xrleltnet xrleltne
17-Nov-08 xrltlet   xrltle
17-Nov-08 xrleidt   xrleid
17-Nov-08 xrletrit  xrletri
17-Nov-08 xrlelttrt xrlelttr
17-Nov-08 xrltletrt xrltletr
17-Nov-08 xrletrt   xrletr
17-Nov-08 xrltnet   xrltne
17-Nov-08 nltpnftt  nltpnft
17-Nov-08 ngtmnftt  ngtmnft
17-Nov-08 xrrebndt  xrrebnd
17-Nov-08 xrret     xrre
17-Nov-08 xrre2t    xrre2
17-Nov-08 eqlet     eqle
17-Nov-08 msqgt0t   msqgt0
17-Nov-08 msqge0t   msqge0
17-Nov-08 gt0ne0t   gt0ne0
17-Nov-08 ne0gt0t   ne0gt0
17-Nov-08 letrit    letric
17-Nov-08 lelttrit  lelttric
17-Nov-08 ltadd1t   ltadd1
17-Nov-08 ltadd2t   ltadd2
17-Nov-08 leadd1t   leadd1
17-Nov-08 leadd2t   leadd2
17-Nov-08 ltsubaddt ltsubadd
17-Nov-08 ltsubadd2t ltsubadd2
17-Nov-08 lesubaddt lesubadd
17-Nov-08 lesubadd2t lesubadd2
17-Nov-08 ltaddsubt ltaddsub
17-Nov-08 ltaddsub2t ltaddsub2
17-Nov-08 leaddsubt leaddsub
17-Nov-08 leaddsub2t leaddsub2
17-Nov-08 sublet    suble
17-Nov-08 lesubt    lesub
17-Nov-08 ltsub23t  ltsub23
17-Nov-08 ltsub13t  ltsub13
17-Nov-08 lt2addt   lt2add
17-Nov-08 le2addt   le2add
17-Nov-08 ltleaddt  ltleadd
17-Nov-08 leltaddt  leltadd
17-Nov-08 addgt0t   addgt0
17-Nov-08 addgegt0t addgegt0
17-Nov-08 addgtge0t addgtge0
17-Nov-08 addge0t   addge0
17-Nov-08 ltaddpost ltaddpos
17-Nov-08 ltaddpos2t ltaddpos2
17-Nov-08 ltsubpost ltsubpos
17-Nov-08 posdift   posdif
17-Nov-08 ltnegt    ltneg
17-Nov-08 ltnegcon1t ltnegcon1
17-Nov-08 lenegt    leneg
17-Nov-08 lenegcon1t lenegcon1
17-Nov-08 lenegcon2t lenegcon2
17-Nov-08 lesub1t   lesub1
17-Nov-08 lesub2t   lesub2
17-Nov-08 ltsub1t   ltsub1
17-Nov-08 ltsub2t   ltsub2
17-Nov-08 lt0neg1t  lt0neg1
17-Nov-08 lt0neg2t  lt0neg2
17-Nov-08 le0neg1t  le0neg1
17-Nov-08 le0neg2t  le0neg2
17-Nov-08 addge01t  addge01
17-Nov-08 addge02t  addge02
17-Nov-08 subge0t   subge0
17-Nov-08 suble0t   suble0
17-Nov-08 subge02t  subge02
17-Nov-08 lesub0t   lesub0
17-Nov-08 mulge0t   mulge0
17-Nov-08 recext    recex
17-Nov-08 mulcant   mulcan
17-Nov-08 mulcan2t  mulcan2
17-Nov-08 mul0ort   mul0or
17-Nov-08 muln0bt   mulne0b
17-Nov-08 muln0t    muln0
17-Nov-08 muleqaddt muleqadd
17-Nov-08 divmult   divmul
17-Nov-08 divmul2t  divmul2
17-Nov-08 divmul3t  divmul3
17-Nov-08 divclt    divcl
17-Nov-08 recclt    reccl
17-Nov-08 divcan1t  divcan1
17-Nov-08 divcan2t  divcan2
17-Nov-08 divne0bt  divne0b
17-Nov-08 divne0t   divne0
17-Nov-08 recne0t   recne0
17-Nov-08 recidt    recid
17-Nov-08 recid2t   recid2
17-Nov-08 divrect   divrec
17-Nov-08 divrec2t  divrec2
17-Nov-08 divasst   divass
17-Nov-08 div23t    div23
17-Nov-08 div13t    div13
17-Nov-08 div12t    div12
17-Nov-08 divdirt   divdir
17-Nov-08 divcan3t  divcan3
17-Nov-08 divcan4t  divcan4
17-Nov-08 div11t    div11
17-Nov-08 dividt    divid
17-Nov-08 div0t     div0
17-Nov-08 diveq0t   diveq0
17-Nov-08 div1t     div1
17-Nov-08 divnegt   divneg
17-Nov-08 divsubdirt divsubdir
17-Nov-08 recrect   recrec
17-Nov-08 rec11rt   rec11r
17-Nov-08 divmuldivt divmuldiv
17-Nov-08 divcan5t  divcan5
17-Nov-08 divmul13t divmul13
17-Nov-08 divmul24t divmul24
17-Nov-08 divadddivt divadddiv
17-Nov-08 divdivdivt divdivdiv
17-Nov-08 recdivt   recdiv
17-Nov-08 divcan6t  divcan6
17-Nov-08 divdiv23t divdiv23
17-Nov-08 divdivmult divdivmul
17-Nov-08 recdiv2t  recdiv2
17-Nov-08 conjmult  conjmul
17-Nov-08 redivclt  redivcl
17-Nov-08 rerecclt  rereccl
17-Nov-08 eqnegt    eqneg
17-Nov-08 negeq0t   negeq0
17-Nov-08 ltp1t     ltp1
17-Nov-08 lep1t     lep1
17-Nov-08 ltm1t     ltm1
17-Nov-08 letrp1t   letrp1
17-Nov-08 p1let     p1le
17-Nov-08 prodgt0t  prodgt0
17-Nov-08 prodgt02t prodgt02
17-Nov-08 prodge0t  prodge0
17-Nov-08 prodge02t prodge02
17-Nov-08 ltmul1t   ltmul1
17-Nov-08 ltmul2t   ltmul2
17-Nov-08 lemul1t   lemul1
17-Nov-08 lemul2t   lemul2
17-Nov-08 lemul1it  lemul1a
17-Nov-08 lemul2it  lemul2a
17-Nov-08 ltmul12it ltmul12a
17-Nov-08 lemul12ait lemul12b
17-Nov-08 lemul12it lemul12a
17-Nov-08 mulgt1t   mulgt1
17-Nov-08 ltmulgt11t ltmulgt11
17-Nov-08 ltmulgt12t ltmulgt12
17-Nov-08 lemulge11t lemulge11
17-Nov-08 ltdiv1t   ltdiv1
17-Nov-08 lediv1t   lediv1
17-Nov-08 gt0divt   gt0div
17-Nov-08 ge0divt   ge0div
17-Nov-08 divgt0t   divgt0
17-Nov-08 divge0t   divge0
17-Nov-08 recgt0t   recgt0
17-Nov-08 ltmuldivt ltmuldiv
17-Nov-08 ltmuldiv2t ltmuldiv2
17-Nov-08 ltdivmult ltdivmul
17-Nov-08 ledivmult ledivmul
17-Nov-08 ltdivmul2t ltdivmul2
17-Nov-08 lt2mul2divt lt2mul2div
17-Nov-08 ledivmul2t ledivmul2
17-Nov-08 lemuldivt lemuldiv
17-Nov-08 lemuldiv2t lemuldiv2
17-Nov-08 ltrect    ltrec
17-Nov-08 lerect    lerec
17-Nov-08 lt2msqt   lt2msq
17-Nov-08 ltdiv2t   ltdiv2
17-Nov-08 ltrec1t   ltrec1
17-Nov-08 lerec2t   lerec2
17-Nov-08 ledivdivt ledivdiv
17-Nov-08 lediv2t   lediv2
17-Nov-08 ltdiv23t  ltdiv23
17-Nov-08 lediv23t  lediv23
17-Nov-08 lediv12it lediv12a
17-Nov-08 lediv2it  lediv2a
17-Nov-08 reclt1t   reclt1
17-Nov-08 recgt1t   recgt1
17-Nov-08 recgt1it  recgt1i
17-Nov-08 recrecltt recreclt
17-Nov-08 le2msqt   le2msq
17-Nov-08 ledivp1t  ledivp1
17-Nov-08 xrmaxltt  xrmaxlt
17-Nov-08 xrltmint  xrltmin
17-Nov-08 maxlet    maxle
17-Nov-08 lemint    lemin
17-Nov-08 maxltt    maxlt
17-Nov-08 ltmint    ltmin
17-Nov-08 nnret     nnre
17-Nov-08 nncnt     nncn
17-Nov-08 nnaddclt  nnaddcl
17-Nov-08 nnmulclt  nnmulcl
17-Nov-08 nn2get    nn2ge
17-Nov-08 nnge1t    nnge1
17-Nov-08 nngt1ne1t nngt1ne1
17-Nov-08 nnle1eq1t nnle1eq1
17-Nov-08 nngt0t    nngt0
17-Nov-08 nnne0t    nnne0
17-Nov-08 nnrecret  nnrecre
17-Nov-08 nnrecgt0t nnrecgt0
17-Nov-08 nnleltp1t nnleltp1
17-Nov-08 nnltp1let nnltp1le
17-Nov-08 nnsubt    nnsub
17-Nov-08 nnaddm1clt nnaddm1cl
17-Nov-08 nndivt    nndiv
17-Nov-08 nndivtrt  nndivtr
17-Nov-08 2timest   2times
17-Nov-08 times2t   times2
17-Nov-08 halfclt   halfcl
17-Nov-08 rehalfclt rehalfcl
17-Nov-08 half0t    half0
17-Nov-08 halfpost  halfpos
17-Nov-08 halfpos2t halfpos2
17-Nov-08 halfnneg2t halfnneg2
17-Nov-08 2halvest  2halves
17-Nov-08 halfaddsubt halfaddsub
17-Nov-08 lt2halvest lt2halves
17-Nov-08 avglet    avgle
17-Nov-08 rpret     rpre
17-Nov-08 rpcnt     rpcn
17-Nov-08 rpgt0t    rpgt0
17-Nov-08 rpge0t    rpge0
17-Nov-08 rpregt0t  rpregt0
17-Nov-08 rpne0t    rpne0
17-Nov-08 rprene0t  rprene0
17-Nov-08 rpcnne0t  rpcnne0
17-Nov-08 rpaddclt  rpaddcl
17-Nov-08 rpmulclt  rpmulcl
17-Nov-08 rpdivclt  rpdivcl
17-Nov-08 rerpdivclt rerpdivcl
17-Nov-08 rpnegt    rpneg
17-Nov-08 nnreclt   nnrecl
17-Nov-08 nnnn0t    nnnn0
17-Nov-08 nn0ret    nn0re
17-Nov-08 nn0cnt    nn0cn
17-Nov-08 nn0ge0t   nn0ge0
17-Nov-08 nn0le0eq0t nn0le0eq0
17-Nov-08 nn0addclt nn0addcl
17-Nov-08 nn0mulclt nn0mulcl
17-Nov-08 nnnn0addclt nnnn0addcl
17-Nov-08 nn0nnaddclt nn0nnaddcl
17-Nov-08 nn0ltp1let nn0ltp1le
17-Nov-08 nn0leltp1t nn0leltp1
17-Nov-08 nn0ltlem1t nn0ltlem1
17-Nov-08 nn0addge1t nn0addge1
17-Nov-08 nn0addge2t nn0addge2
17-Nov-08 zret      zre
17-Nov-08 zcnt      zcn
17-Nov-08 nnzt      nnz
17-Nov-08 nn0zt     nn0z
17-Nov-08 znnnlt1t  znnnlt1
17-Nov-08 nn0subt   nn0sub
17-Nov-08 nn0sub2t  nn0sub2
17-Nov-08 znegclt   znegcl
17-Nov-08 zaddclt   zaddcl
17-Nov-08 zsubclt   zsubcl
17-Nov-08 zrevaddclt zrevaddcl
17-Nov-08 nn0p1nnt  nn0p1nn
17-Nov-08 nnm1nn0t  nnm1nn0
17-Nov-08 znnsubt   znnsub
17-Nov-08 znn0subt  znn0sub
17-Nov-08 znn0sub2t znn0sub2
17-Nov-08 zmulclt   zmulcl
17-Nov-08 zltp1let  zltp1le
17-Nov-08 zleltp1t  zleltp1
17-Nov-08 zlem1ltt  zlem1lt
17-Nov-08 zltlem1t  zltlem1
17-Nov-08 nn0lem1ltt nn0lem1lt
17-Nov-08 nnlem1ltt nnlem1lt
17-Nov-08 nnltlem1t nnltlem1
17-Nov-08 zdivt     zdiv
17-Nov-08 zdivaddt  zdivadd
17-Nov-08 zdivmult  zdivmul
17-Nov-08 z2get     z2ge
17-Nov-08 zextlet   zextle
17-Nov-08 zextltt   zextlt
17-Nov-08 recnzt    recnz
17-Nov-08 btwnnzt   btwnnz
17-Nov-08 gtndivt   gtndiv
17-Nov-08 primet    prime
17-Nov-08 nneot     nneo
17-Nov-08 zeot      zeo
17-Nov-08 qret      qre
17-Nov-08 zqt       zq
17-Nov-08 nnqt      nnq
17-Nov-08 qcnt      qcn
17-Nov-08 qaddclt   qaddcl
17-Nov-08 qnegclt   qnegcl
17-Nov-08 qmulclt   qmulcl
17-Nov-08 qsubclt   qsubcl
17-Nov-08 qrecclt   qreccl
17-Nov-08 qdivclt   qdivcl
17-Nov-08 qrevaddclt qrevaddcl
17-Nov-08 nnrecqt   nnrecq
17-Nov-08 irraddt   irradd
17-Nov-08 irrmult   irrmul
17-Nov-08 flvalt    flval
17-Nov-08 flclt     flcl
17-Nov-08 flreclt   flrecl
17-Nov-08 flleltt   fllelt
17-Nov-08 fllet     flle
17-Nov-08 flltp1t   flltp1
17-Nov-08 fraclt1t  fraclt1
17-Nov-08 fracge0t  fracge0
17-Nov-08 flget     flge
17-Nov-08 flltt     fllt
17-Nov-08 flidt     flid
17-Nov-08 flidmt    flidm
17-Nov-08 flidzt    flidz
17-Nov-08 flwordit  flwordi
17-Nov-08 flval2t   flval2
17-Nov-08 flval3t   flval3
17-Nov-08 flbit     flbi
17-Nov-08 flbi2t    flbi2
17-Nov-08 flge0nn0t flge0nn0
17-Nov-08 flge1nnt  flge1nn
17-Nov-08 fladdzt   fladdz
17-Nov-08 btwnzge0t btwnzge0
17-Nov-08 flhalft   flhalf
17-Nov-08 ceiclt    ceicl
17-Nov-08 ceiget    ceige
17-Nov-08 ceim1lt   ceim1l
17-Nov-08 ceilet    ceile
17-Nov-08 fldivt    fldiv
17-Nov-08 fldiv2t   fldiv2
17-Nov-08 modvalt   modval
17-Nov-08 modclt    modcl
17-Nov-08 modge0t   modge0
17-Nov-08 modltt    modlt
17-Nov-08 modfract  modfrac
17-Nov-08 flmodt    flmod
17-Nov-08 modcyct   modcyc
17-Nov-08 modcyc2t  modcyc2
17-Nov-08 modadd1t  modadd1
17-Nov-08 modmul1t  modmul1
17-Nov-08 moddit    moddi
17-Nov-08 modirrt   modirr
17-Nov-08 ioovalt   iooval
17-Nov-08 iooval2t  iooval2
17-Nov-08 ioo0t     ioo0
17-Nov-08 ioon0t    ioon0
17-Nov-08 iooint    iooin
17-Nov-08 iocvalt   iocval
17-Nov-08 icovalt   icoval
17-Nov-08 iccvalt   iccval
17-Nov-08 elioo1t   elioo1
17-Nov-08 elioo2t   elioo2
17-Nov-08 elioc1t   elioc1
17-Nov-08 elico1t   elico1
17-Nov-08 elicc1t   elicc1
17-Nov-08 elioo5t   elioo5
17-Nov-08 eliooret  elioore
17-Nov-08 eliooxrt  eliooxr
17-Nov-08 eliooordt eliooord
17-Nov-08 elioc2t   elioc2
17-Nov-08 elico2t   elico2
17-Nov-08 elicc2t   elicc2
17-Nov-08 iooshft   iooshf
17-Nov-08 iccssret  iccssre
17-Nov-08 lbicc2t   lbicc2
17-Nov-08 ubicc2t   ubicc2
17-Nov-08 ioonegt   iooneg
17-Nov-08 iccnegt   iccneg
17-Nov-08 icoshft   icoshf
17-Nov-08 ioojoint  ioojoin
17-Nov-08 uzvalt    uzval
17-Nov-08 eluz1t    eluz1
17-Nov-08 eluz2t    eluz2
17-Nov-08 eluzt     eluz
17-Nov-08 uzidt     uzid
17-Nov-08 uznegit   uznegi
17-Nov-08 uz11t     uz11
17-Nov-08 eluzp1m1t eluzp1m1
17-Nov-08 eluzp1lt  eluzp1l
17-Nov-08 eluzp1p1t eluzp1p1
17-Nov-08 uzaddclt  uzaddcl
17-Nov-08 fzvalt    fzval
17-Nov-08 elfz1t    elfz1
17-Nov-08 elfzt     elfz
17-Nov-08 elfz2t    elfz2
17-Nov-08 elfz5t    elfz5
17-Nov-08 elfz4t    elfz4
17-Nov-08 eluzfzt   eluzfz
17-Nov-08 elfzuz3t  elfzuz3
17-Nov-08 elfzuz2t  elfzuz2
17-Nov-08 eluzfz1t  eluzfz1
17-Nov-08 elfzuzt   elfzuz
17-Nov-08 eluzfz2t  eluzfz2
17-Nov-08 elfz3t    elfz3
17-Nov-08 elfz1eqt  elfz1eq
17-Nov-08 fznt      fzn
17-Nov-08 elfznnt   elfznn
17-Nov-08 elfz2nn0t elfz2nn0
17-Nov-08 elfznn0t  elfznn0
17-Nov-08 elfz3nn0t elfz3nn0
17-Nov-08 fznn0subt fznn0sub
17-Nov-08 fznn0sub2t fznn0sub2
17-Nov-08 fzaddelt  fzaddel
17-Nov-08 fzsubelt  fzsubel
17-Nov-08 fzoptht   fzopth
17-Nov-08 fzss1t    fzss1
17-Nov-08 fzss2t    fzss2
17-Nov-08 fzssuzt   fzssuz
17-Nov-08 fzssp1t   fzssp1
17-Nov-08 fzp1sst   fzp1ss
17-Nov-08 fzelp1t   fzelp1
17-Nov-08 fzrevt    fzrev
17-Nov-08 fzrev2t   fzrev2
17-Nov-08 fzrev2it  fzrev2i
17-Nov-08 fzrev3t   fzrev3
17-Nov-08 fzrev3it  fzrev3i
17-Nov-08 fznn0t    fznn0
17-Nov-08 fz1sbct   fz1sbc
17-Nov-08 fzneuzt   fzneuz
17-Nov-08 fzrevralt fzrevral
17-Nov-08 fzrevral2t fzrevral2
17-Nov-08 fzrevral3t fzrevral3
17-Nov-08 fzshftralt fzshftral
17-Nov-08 ser1ft    ser1f
17-Nov-08 limsupvalt limsupval
17-Nov-08 limsupclt limsupcl
17-Nov-08 expvalt   expval
17-Nov-08 exp0t     exp0
17-Nov-08 expnnvalt expnnval
17-Nov-08 exp1t     exp1
17-Nov-08 expp1t    expp1
17-Nov-08 nnexpclt  nnexpcl
17-Nov-08 nn0expclt nn0expcl
17-Nov-08 zexpclt   zexpcl
17-Nov-08 qexpclt   qexpcl
17-Nov-08 reexpclt  reexpcl
17-Nov-08 expclt    expcl
17-Nov-08 rpexpclt  rpexpcl
17-Nov-08 expm1t    expm1
17-Nov-08 1expt     1exp
17-Nov-08 expeq0t   expeq0
17-Nov-08 expne0t   expne0
17-Nov-08 expne0it  expne0i
17-Nov-08 expgt0t   expgt0
17-Nov-08 0expt     0exp
17-Nov-08 expge0t   expge0
17-Nov-08 expgt1t   expgt1
17-Nov-08 expge1t   expge1
17-Nov-08 mulexpt   mulexp
17-Nov-08 recexpt   recexp
17-Nov-08 expaddt   expadd
17-Nov-08 expmult   expmul
17-Nov-08 expsubt   expsub
17-Nov-08 divexpt   divexp
17-Nov-08 expordit  expordi
17-Nov-08 expcant   expcan
17-Nov-08 expordt   expord
17-Nov-08 expwordit expwordi
17-Nov-08 expord2t  expord2
17-Nov-08 expword2it expword2i
17-Nov-08 expmwordit expmwordi
17-Nov-08 exple1t   exple1
17-Nov-08 expubndt  expubnd
17-Nov-08 sqvalt    sqval
17-Nov-08 sqnegt    sqneg
17-Nov-08 sqclt     sqcl
17-Nov-08 sqmult    sqmul
17-Nov-08 sqeq0t    sqeq0
17-Nov-08 sqne0t    sqne0
17-Nov-08 resqclt   resqcl
17-Nov-08 sqgt0t    sqgt0
17-Nov-08 sq11t     sq11
17-Nov-08 lt2sqt    lt2sq
17-Nov-08 le2sqt    le2sq
17-Nov-08 le2sqit   le2sq2
17-Nov-08 sqge0t    sqge0
17-Nov-08 sqlecant  sqlecan
17-Nov-08 subsqt    subsq
17-Nov-08 subsq2t   subsq2
17-Nov-08 sqeqort   sqeqor
17-Nov-08 binom2t   binom2
17-Nov-08 sq01t     sq01
17-Nov-08 expnbndt  expnbnd
17-Nov-08 expnlbndt expnlbnd
17-Nov-08 expnlbnd2t expnlbnd2
17-Nov-08 nn0opth2t nn0opth2
17-Nov-08 sqrclt    sqrcl
17-Nov-08 sqrgt0t   sqrgt0
17-Nov-08 sqrge0t   sqrge0
17-Nov-08 sqrlet    sqrle
17-Nov-08 sqr00t    sqr00
17-Nov-08 rpsqrclt  rpsqrcl
17-Nov-08 sqrsqt    sqrsq
17-Nov-08 sqsqrt    sqsqr
17-Nov-08 crut      cru
17-Nov-08 revalt    reval
17-Nov-08 imvalt    imval
17-Nov-08 reclt     recl
17-Nov-08 imclt     imcl
17-Nov-08 replimt   replim
17-Nov-08 absvalt   absval
17-Nov-08 cjvalt    cjval
17-Nov-08 cjclt     cjcl
17-Nov-08 crret     crre
17-Nov-08 crimt     crim
17-Nov-08 imret     imre
17-Nov-08 reim0t    reim0
17-Nov-08 reim0bt   reim0b
17-Nov-08 rerebt    rereb
17-Nov-08 mulret    mulre
17-Nov-08 reret     rere
17-Nov-08 cjrebt    cjreb
17-Nov-08 cjmulrclt cjmulrcl
17-Nov-08 cjmulvalt cjmulval
17-Nov-08 cjmulge0t cjmulge0
17-Nov-08 renegt    reneg
17-Nov-08 readdt    readd
17-Nov-08 resubt    resub
17-Nov-08 imnegt    imneg
17-Nov-08 imaddt    imadd
17-Nov-08 imsubt    imsub
17-Nov-08 cjret     cjre
17-Nov-08 cjcjt     cjcj
17-Nov-08 cjaddt    cjadd
17-Nov-08 cjmult    cjmul
17-Nov-08 cjnegt    cjneg
17-Nov-08 addcjt    addcj
17-Nov-08 cjsubt    cjsub
17-Nov-08 cjexpt    cjexp
17-Nov-08 recjt     recj
17-Nov-08 imcjt     imcj
17-Nov-08 cjreimt   cjreim
17-Nov-08 cjreim2t  cjreim2
17-Nov-08 cj11t     cj11
17-Nov-08 cjne0t    cjne0
17-Nov-08 absnegt   absneg
17-Nov-08 absclt    abscl
17-Nov-08 abscjt    abscj
17-Nov-08 absvalsqt absvalsq
17-Nov-08 absvalsq2t absvalsq2
17-Nov-08 sqabsaddt sqabsadd
17-Nov-08 sqabssubt sqabssub
17-Nov-08 absval2t  absval2
17-Nov-08 abs00t    abs00
17-Nov-08 absge0t   absge0
17-Nov-08 absrpclt  absrpcl
17-Nov-08 absreimsqt absreimsq
17-Nov-08 absreimt  absreim
17-Nov-08 absmult   absmul
17-Nov-08 absdivt   absdiv
17-Nov-08 absidt    absid
17-Nov-08 absnidt   absnid
17-Nov-08 leabst    leabs
17-Nov-08 absort    absor
17-Nov-08 absret    absre
17-Nov-08 absresqt  absresq
17-Nov-08 absexpt   absexp
17-Nov-08 absrelet  absrele
17-Nov-08 absimlet  absimle
17-Nov-08 nn0absclt nn0abscl
17-Nov-08 absltt    abslt
17-Nov-08 abslet    absle
17-Nov-08 abssubne0t abssubne0
17-Nov-08 absdifltt absdiflt
17-Nov-08 absdiflet absdifle
17-Nov-08 lenegsqt  lenegsq
17-Nov-08 releabst  releabs
17-Nov-08 cjdivt    cjdiv
17-Nov-08 absidmt   absidm
17-Nov-08 absgt0t   absgt0
17-Nov-08 abssubt   abssub
17-Nov-08 abssubge0t abssubge0
17-Nov-08 abssuble0t abssuble0
17-Nov-08 absmaxt   absmax
17-Nov-08 abstrit   abstri
17-Nov-08 abs3dift  abs3dif
17-Nov-08 abs2dift  abs2dif
17-Nov-08 abs2difabst abs2difabs
17-Nov-08 recant    recan
17-Nov-08 abs3lemt  abs3lem
17-Nov-08 facnnt    facnn
17-Nov-08 facp1t    facp1
17-Nov-08 facnn2t   facnn2
17-Nov-08 facclt    faccl
17-Nov-08 facne0t   facne0
17-Nov-08 facdivt   facdiv
17-Nov-08 facndivt  facndiv
17-Nov-08 facwordit facwordi
17-Nov-08 facavgt   facavg
17-Nov-08 bcvalt    bcval
17-Nov-08 bcval2t   bcval2
17-Nov-08 bcval3t   bcval3
17-Nov-08 bcval4t   bcval4
17-Nov-08 bccmplt   bccmpl
17-Nov-08 bcn0t     bcn0
17-Nov-08 bcnnt     bcnn
17-Nov-08 bcnp11t   bcnp11
17-Nov-08 bcnp1nt   bcnp1n
17-Nov-08 bcpasc2t  bcpasc2
17-Nov-08 bcpasct   bcpasc
17-Nov-08 bccl2t    bccl2
17-Nov-08 bcclt     bccl
17-Nov-08 permnnt   permnn
17-Nov-08 fsumclt   fsumcl
17-Nov-08 fsum0clt  fsum0cl
17-Nov-08 fsumreclt fsumrecl
17-Nov-08 fsumsplit fsumspli
17-Nov-08 fsum0split fsum0spli
17-Nov-08 fsumshft  fsumshf
17-Nov-08 fsumconst fsumcons
17-Nov-08 clmi2at   clmi2a
17-Nov-08 caucvg3t  caucvg3
17-Nov-08 eftclt    eftcl
17-Nov-08 efvalt    efval
17-Nov-08 efclt     efcl
17-Nov-08 reefclt   reefcl
17-Nov-08 efcjt     efcj
17-Nov-08 efaddt    efadd
17-Nov-08 efcant    efcan
17-Nov-08 efne0t    efne0
17-Nov-08 efsubt    efsub
17-Nov-08 efexpt    efexp
17-Nov-08 efnn0valt efnn0val
17-Nov-08 reeftclt  reeftcl
17-Nov-08 eftlubclt eftlubcl
17-Nov-08 efgt0t    efgt0
17-Nov-08 reef11t   reef11
17-Nov-08 eflegeot  eflegeo
17-Nov-08 efm1legeot efm1legeo
17-Nov-08 sinvalt   sinval
17-Nov-08 cosvalt   cosval
17-Nov-08 sinclt    sincl
17-Nov-08 cosclt    coscl
17-Nov-08 resinvalt resinval
17-Nov-08 recosvalt recosval
17-Nov-08 resinclt  resincl
17-Nov-08 recosclt  recoscl
17-Nov-08 sinnegt   sinneg
17-Nov-08 cosnegt   cosneg
17-Nov-08 efivalt   efival
17-Nov-08 efmivalt  efmival
17-Nov-08 efeult    efeul
17-Nov-08 sinaddt   sinadd
17-Nov-08 cosaddt   cosadd
17-Nov-08 sinsubt   sinsub
17-Nov-08 cossubt   cossub
17-Nov-08 addsint   addsin
17-Nov-08 subsint   subsin
17-Nov-08 addcost   addcos
17-Nov-08 subcost   subcos
17-Nov-08 sincossqt sincossq
17-Nov-08 sin2tt    sin2t
17-Nov-08 cos2tt    cos2t
17-Nov-08 cos2tsint cos2tsin
17-Nov-08 sinbndt   sinbnd
17-Nov-08 cosbndt   cosbnd
17-Nov-08 absefit   absefi
17-Nov-08 abseft    absef
17-Nov-08 absefibt  absefib
17-Nov-08 cosh111t  cosh111
17-Nov-08 logclt    logcl
17-Nov-08 relogclt  relogcl
17-Nov-08 eflogt    eflog
17-Nov-08 reeflogt  reeflog
17-Nov-08 logeft    logef
17-Nov-08 relogeft  relogef
17-Nov-08 relogmult relogmul
17-Nov-08 relogdivt relogdiv
17-Nov-08 explogt   explog
17-Nov-08 reexplogt reexplog
17-Nov-08 relogexpt relogexp
17-Nov-08 logltbt   logltb
17-Nov-08 1p1times  1p1timesi
17-Nov-08 2climnn   2climnni
17-Nov-08 2climnn0  2climnn0i
17-Nov-08 2shft     2shfti
17-Nov-08 2times    2timesi
17-Nov-08 abs00     abs00i
17-Nov-08 abs1m     abs1mi
17-Nov-08 abs3dif   abs3difi
17-Nov-08 abscj     abscji
17-Nov-08 abscl     abscli
17-Nov-08 absdivz   absdivzi
17-Nov-08 absef01tlub absef01tlubi
17-Nov-08 absefm1le absefm1lei
17-Nov-08 absge0    absge0i
17-Nov-08 absgt0    absgt0i
17-Nov-08 absid     absidi
17-Nov-08 absle     abslei
17-Nov-08 abslt     abslti
17-Nov-08 absmul    absmuli
17-Nov-08 absneg    absnegi
17-Nov-08 absnid    absnidi
17-Nov-08 absor     absori
17-Nov-08 abspef01tlub abspef01tlubi
17-Nov-08 absre     absrei
17-Nov-08 abssub    abssubi
17-Nov-08 abstri    abstrii
17-Nov-08 absval2   absval2i
17-Nov-08 absvalsq  absvalsqi
17-Nov-08 absvalsq2 absvalsq2i
17-Nov-08 add12     add12i
17-Nov-08 add20     add20i
17-Nov-08 add23     add23i
17-Nov-08 add4      add4i
17-Nov-08 add42     add42i
17-Nov-08 addass    addassi
17-Nov-08 addcan    addcani
17-Nov-08 addcan2   addcan2i
17-Nov-08 addcj     addcji
17-Nov-08 addcl     addcli
17-Nov-08 addcom    addcomi
17-Nov-08 adddi     adddii
17-Nov-08 adddir    adddiri
17-Nov-08 addge0    addge0i
17-Nov-08 addgegt0  addgegt0i
17-Nov-08 addgt0    addgt0i
17-Nov-08 addgt0i   addgt0ii
17-Nov-08 addid1    addid1i
17-Nov-08 addid2    addid2i
17-Nov-08 addsub    addsubi
17-Nov-08 addsub4   addsub4i
17-Nov-08 addsubass addsubassi
17-Nov-08 bcpasc    bcpasci
17-Nov-08 bcpasc2   bcpasc2i
17-Nov-08 binom     binomi
17-Nov-08 binom1p   binom1pi
17-Nov-08 binom2    binom2i
17-Nov-08 binom2a   binom2ai
17-Nov-08 cau2      cau2i
17-Nov-08 cau3      cau3i
17-Nov-08 cau3i     cau3ii
17-Nov-08 cau3ir    cau3iri
17-Nov-08 cau4i     cau4ii
17-Nov-08 cau5      cau5i
17-Nov-08 cau5i     cau5ii
17-Nov-08 caubnd    caubndi
17-Nov-08 caucvg    caucvgi
17-Nov-08 caucvg2   caucvg2i
17-Nov-08 caucvg3   caucvg3i
17-Nov-08 caucvg3a  caucvg3ai
17-Nov-08 cauim     cauimi
17-Nov-08 caure     caurei
17-Nov-08 cbvsum    cbvsumi
17-Nov-08 cjadd     cjaddi
17-Nov-08 cjcj      cjcji
17-Nov-08 cjcl      cjcli
17-Nov-08 cjdiv     cjdivi
17-Nov-08 cjmul     cjmuli
17-Nov-08 cjmulge0  cjmulge0i
17-Nov-08 cjmulrcl  cjmulrcli
17-Nov-08 cjmulval  cjmulvali
17-Nov-08 cjneg     cjnegi
17-Nov-08 cjreb     cjrebi
17-Nov-08 clim2serz clim2serzi
17-Nov-08 clim2serzt clim2serzti
17-Nov-08 climabs   climabsi
17-Nov-08 climabs0  climabs0i
17-Nov-08 climadd   climaddi
17-Nov-08 climaddc  climaddci
17-Nov-08 climaddc1 climaddc1i
17-Nov-08 climaddc2 climaddc2i
17-Nov-08 climcau   climcaui
17-Nov-08 climcj    climcji
17-Nov-08 climcmp   climcmpi
17-Nov-08 climcmpc1 climcmpc1i
17-Nov-08 climconst climconsti
17-Nov-08 climeu    climeui
17-Nov-08 climfnrcl climfnrcli
17-Nov-08 climge0   climge0i
17-Nov-08 climim    climimi
17-Nov-08 climmul   climmuli
17-Nov-08 climmulc  climmulci
17-Nov-08 climmulc2 climmulc2i
17-Nov-08 climre    climrei
17-Nov-08 climrecl  climrecli
17-Nov-08 climres   climresi
17-Nov-08 climreu   climreui
17-Nov-08 climserzle climserzlei
17-Nov-08 climshft  climshfti
17-Nov-08 climshft2 climshft2i
17-Nov-08 climsqueeze climsqueezei
17-Nov-08 climsqueeze2 climsqueeze2i
17-Nov-08 climsub   climsubi
17-Nov-08 climsubc2 climsubc2i
17-Nov-08 climsup   climsupi
17-Nov-08 climub    climubi
17-Nov-08 climubi   climubii
17-Nov-08 climuni   climunii
17-Nov-08 climunii  climuniii
17-Nov-08 climuz0   climuz0i
17-Nov-08 clm0      clm0i
17-Nov-08 clm0i     clm0ii
17-Nov-08 clm0nns   clm0nnsi
17-Nov-08 clm1      clm1i
17-Nov-08 clm2      clm2i
17-Nov-08 clm3      clm3i
17-Nov-08 clm4      clm4i
17-Nov-08 clm4at    clm4ati
17-Nov-08 clm4f     clm4fi
17-Nov-08 clm4le    clm4lei
17-Nov-08 clmi1     clmi1i
17-Nov-08 clmi2     clmi2i
17-Nov-08 clmi2rp   clmi2rpi
17-Nov-08 clmnns    clmnnsi
17-Nov-08 cnegex    cnegexi
17-Nov-08 cosadd    cosaddi
17-Nov-08 crim      crimi
17-Nov-08 crmul     crmuli
17-Nov-08 crne0     crne0i
17-Nov-08 crre      crrei
17-Nov-08 crrecz    crreczi
17-Nov-08 cru       crui
17-Nov-08 cvg1      cvg1i
17-Nov-08 cvg1i     cvg1ii
17-Nov-08 cvg2      cvg2i
17-Nov-08 cvg3      cvg3i
17-Nov-08 cvganuz   cvganuzi
17-Nov-08 cvgcmp    cvgcmpi
17-Nov-08 cvgcmp2   cvgcmp2i
17-Nov-08 cvgcmp2c  cvgcmp2ci
17-Nov-08 cvgcmp3c  cvgcmp3ci
17-Nov-08 cvgcmp3ce cvgcmp3cei
17-Nov-08 cvgcmp3cet cvgcmp3ceti
17-Nov-08 cvgcmpub  cvgcmpubi
17-Nov-08 cvgrat    cvgrati
17-Nov-08 dfef2     dfef2i
17-Nov-08 dfuz      dfuzi
17-Nov-08 div0      div0i
17-Nov-08 div1      div1i
17-Nov-08 div11     div11i
17-Nov-08 div23     div23i
17-Nov-08 divadddiv divadddivi
17-Nov-08 divass    divassi
17-Nov-08 divassz   divasszi
17-Nov-08 divcan1   divcan1i
17-Nov-08 divcan1z  divcan1zi
17-Nov-08 divcan2   divcan2i
17-Nov-08 divcan2z  divcan2zi
17-Nov-08 divcan3   divcan3i
17-Nov-08 divcan3z  divcan3zi
17-Nov-08 divcan4   divcan4i
17-Nov-08 divcan4z  divcan4zi
17-Nov-08 divcl     divcli
17-Nov-08 divclz    divclzi
17-Nov-08 divdir    divdiri
17-Nov-08 divdirz   divdirzi
17-Nov-08 divdiv23  divdiv23i
17-Nov-08 divdiv23z divdiv23zi
17-Nov-08 divdivdiv divdivdivi
17-Nov-08 divge0    divge0i
17-Nov-08 divgt0    divgt0i
17-Nov-08 divgt0i   divgt0ii
17-Nov-08 divgt0i2  divgt0i2i
17-Nov-08 divid     dividi
17-Nov-08 divmul    divmuli
17-Nov-08 divmul13  divmul13i
17-Nov-08 divmuldiv divmuldivi
17-Nov-08 divmulz   divmulzi
17-Nov-08 divne0    divne0i
17-Nov-08 divrec    divreci
17-Nov-08 divrecz   divreczi
17-Nov-08 divval    divvali
17-Nov-08 dsupivth  dsupivthi
17-Nov-08 ef01tlub  ef01tlubi
17-Nov-08 ef1tlub   ef1tlubi
17-Nov-08 ef4p      ef4pi
17-Nov-08 efadd     efaddi
17-Nov-08 efcj      efcji
17-Nov-08 effsumle  effsumlei
17-Nov-08 efge1     efge1i
17-Nov-08 efge1p    efge1pi
17-Nov-08 efgt0     efgt0i
17-Nov-08 efgt1     efgt1i
17-Nov-08 eflegeo   eflegeoi
17-Nov-08 eflt      eflti
17-Nov-08 efltb     efltbi
17-Nov-08 efm1legeo efm1legeoi
17-Nov-08 efm1lim   efm1limi
17-Nov-08 efsep     efsepi
17-Nov-08 eft0val   eft0vali
17-Nov-08 eftabs    eftabsi
17-Nov-08 eftlclt   eftlclti
17-Nov-08 eftlext   eftlexti
17-Nov-08 elcncf1d  elcncf1di
17-Nov-08 elcncf1i  elcncf1ii
17-Nov-08 elfzel2   elfzel2i
17-Nov-08 elrpi     elrpii
17-Nov-08 eluz1     eluz1i
17-Nov-08 eluzaddi  eluzaddii
17-Nov-08 eluzsubi  eluzsubii
17-Nov-08 eqle      eqlei
17-Nov-08 eqneg     eqnegi
17-Nov-08 expcnv    expcnvi
17-Nov-08 fnsmnt    fnsmnti
17-Nov-08 fseqsupub fseqsupubi
17-Nov-08 fsum1     fsum1i
17-Nov-08 fsum1f    fsum1fi
17-Nov-08 fsum2     fsum2i
17-Nov-08 fsum3     fsum3i
17-Nov-08 fsum4     fsum4i
17-Nov-08 fsump1    fsump1i
17-Nov-08 fsump1f   fsump1fi
17-Nov-08 fsumser0f fsumser0fi
17-Nov-08 fsumser1f fsumser1fi
17-Nov-08 fsumserz  fsumserzi
17-Nov-08 fsumserz2 fsumserz2i
17-Nov-08 fsumserzf fsumserzfi
17-Nov-08 fzelp1    fzelp1i
17-Nov-08 geoser    geoseri
17-Nov-08 geosum    geosumi
17-Nov-08 gt0ne0    gt0ne0i
17-Nov-08 gt0ne0i   gt0ne0ii
17-Nov-08 halfpos   halfposi
17-Nov-08 hbneg     hbnegi
17-Nov-08 hbnegd    hbnegdi
17-Nov-08 hbsum     hbsumi
17-Nov-08 hbsum1    hbsum1i
17-Nov-08 icoshftf1oi icoshftf1oii
17-Nov-08 imadd     imaddi
17-Nov-08 imcj      imcji
17-Nov-08 imcl      imcli
17-Nov-08 immul     immuli
17-Nov-08 imneg     imnegi
17-Nov-08 infcvg    infcvgiOLD
17-Nov-08 infcvgaux1 infcvgaux1i
17-Nov-08 infcvgaux2 infcvgaux2i
17-Nov-08 ipcn      ipcni
17-Nov-08 iserzabs  iserzabsi
17-Nov-08 iserzcmp  iserzcmpi
17-Nov-08 iserzcmp0 iserzcmp0i
17-Nov-08 iserzex   iserzexi
17-Nov-08 iserzext  iserzexti
17-Nov-08 iserzgt0  iserzgt0i
17-Nov-08 iserzmulc1 iserzmulc1i
17-Nov-08 iserzshft iserzshfti
17-Nov-08 iserzshft2 iserzshft2i
17-Nov-08 isum0split isum0spliti
17-Nov-08 isum1clim isum1climi
17-Nov-08 isum1p    isum1pi
17-Nov-08 isumclim2t isumclim2ti
17-Nov-08 isumclim2tf isumclim2tfi
17-Nov-08 isumclim3t isumclim3ti
17-Nov-08 isumclim4t isumclim4ti
17-Nov-08 isumclim5t isumclim5ti
17-Nov-08 isumclimt isumclimti
17-Nov-08 isumclimtf isumclimtfi
17-Nov-08 isumclt   isumclti
17-Nov-08 isumcmpi  isumcmpii
17-Nov-08 isummulc1 isummulc1i
17-Nov-08 isummulc1ALT isummulc1iALT
17-Nov-08 isummulc1a isummulc1ai
17-Nov-08 isumnn0nn isumnn0nni
17-Nov-08 isumnn0nna isumnn0nnai
17-Nov-08 isumnul   isumnuli
17-Nov-08 isumreclt isumreclti
17-Nov-08 isumshft  isumshfti
17-Nov-08 isumshft2 isumshft2i
17-Nov-08 isumsplit isumspliti
17-Nov-08 isumval2t isumval2ti
17-Nov-08 isumvalt  isumvalti
17-Nov-08 isumvaltf isumvaltfi
17-Nov-08 isupivth  isupivthi
17-Nov-08 le2add    le2addi
17-Nov-08 le2msq    le2msqi
17-Nov-08 le2sq     le2sqi
17-Nov-08 le2tri3   le2tri3i
17-Nov-08 leabs     leabsi
17-Nov-08 leadd1    leadd1i
17-Nov-08 leadd2    leadd2i
17-Nov-08 lecase    lecasei
17-Nov-08 ledivp1   ledivp1i
17-Nov-08 leid      leidi
17-Nov-08 leloe     leloei
17-Nov-08 lelttr    lelttri
17-Nov-08 lelttrd   lelttrdi
17-Nov-08 lemul1    lemul1i
17-Nov-08 lemul2    lemul2i
17-Nov-08 leneg     lenegi
17-Nov-08 lenegcon1 lenegcon1i
17-Nov-08 lenlt     lenlti
17-Nov-08 lerec     lereci
17-Nov-08 lesub0    lesub0i
17-Nov-08 lesubadd  lesubaddi
17-Nov-08 lesubadd2 lesubadd2i
17-Nov-08 letr      letri
17-Nov-08 letrd     letrdi
17-Nov-08 letri     letrii
17-Nov-08 letri3    letri3i
17-Nov-08 lt2add    lt2addi
17-Nov-08 lt2msq    lt2msqi
17-Nov-08 lt2sq     lt2sqi
17-Nov-08 ltadd1    ltadd1i
17-Nov-08 ltadd2    ltadd2i
17-Nov-08 ltaddpos  ltaddposi
17-Nov-08 ltaddsub  ltaddsubi
17-Nov-08 ltdiv1    ltdiv1i
17-Nov-08 ltdiv1i   ltdiv1ii
17-Nov-08 ltdiv23   ltdiv23i
17-Nov-08 ltdiv23i  ltdiv23ii
17-Nov-08 ltdivp1   ltdivp1i
17-Nov-08 ltle      ltlei
17-Nov-08 ltlei     ltleii
17-Nov-08 ltlen     ltleni
17-Nov-08 ltletr    ltletri
17-Nov-08 ltletrd   ltletrdi
17-Nov-08 ltmul1    ltmul1i
17-Nov-08 ltmul1i   ltmul1ii
17-Nov-08 ltmul2    ltmul2i
17-Nov-08 ltmuldiv  ltmuldivi
17-Nov-08 ltne      ltnei
17-Nov-08 ltneg     ltnegi
17-Nov-08 ltnegcon1 ltnegcon1i
17-Nov-08 ltnegcon2 ltnegcon2i
17-Nov-08 ltnle     ltnlei
17-Nov-08 ltnr      ltnri
17-Nov-08 ltnsym    ltnsymi
17-Nov-08 ltp1      ltp1i
17-Nov-08 ltrec     ltreci
17-Nov-08 ltreci    ltrecii
17-Nov-08 ltsubadd  ltsubaddi
17-Nov-08 ltsubadd2 ltsubadd2i
17-Nov-08 lttr      lttri
17-Nov-08 lttrd     lttrdi
17-Nov-08 lttri2    lttri2i
17-Nov-08 lttri3    lttri3i
17-Nov-08 msq0      msq0i
17-Nov-08 msq11     msq11i
17-Nov-08 msqge0    msqge0i
17-Nov-08 msqgt0    msqgt0i
17-Nov-08 mul01     mul01i
17-Nov-08 mul02     mul02i
17-Nov-08 mul0or    mul0ori
17-Nov-08 mul12     mul12i
17-Nov-08 mul23     mul23i
17-Nov-08 mul2neg   mul2negi
17-Nov-08 mul4      mul4i
17-Nov-08 muladd    muladdi
17-Nov-08 mulass    mulassi
17-Nov-08 mulcan    mulcani
17-Nov-08 mulcant2  mulcant2i
17-Nov-08 mulcl     mulcli
17-Nov-08 mulcom    mulcomi
17-Nov-08 mulge0    mulge0i
17-Nov-08 mulgt0    mulgt0i
17-Nov-08 mulgt0i   mulgt0ii
17-Nov-08 mulid1    mulid1i
17-Nov-08 mulid2    mulid2i
17-Nov-08 mulm1     mulm1i
17-Nov-08 muln0     mulne0i
17-Nov-08 mulneg1   mulneg1i
17-Nov-08 mulneg2   mulneg2i
17-Nov-08 neg11     neg11i
17-Nov-08 negcl     negcli
17-Nov-08 negcon1   negcon1i
17-Nov-08 negcon2   negcon2i
17-Nov-08 negdi     negdii
17-Nov-08 negeu     negeui
17-Nov-08 negfcncf  negfcncfi
17-Nov-08 negid     negidi
17-Nov-08 negn0     negn0i
17-Nov-08 negne0    negne0i
17-Nov-08 negneg    negnegi
17-Nov-08 negreb    negrebi
17-Nov-08 negsub    negsubi
17-Nov-08 negsubdi  negsubdii
17-Nov-08 negsubdi2 negsubdi2i
17-Nov-08 nn0addcl  nn0addcli
17-Nov-08 nn0addge1 nn0addge1i
17-Nov-08 nn0addge2 nn0addge2i
17-Nov-08 nn0cn     nn0cni
17-Nov-08 nn0ge0    nn0ge0i
17-Nov-08 nn0le2msqt nn0le2msqti
17-Nov-08 nn0le2x   nn0le2xi
17-Nov-08 nn0lele2x nn0lele2xi
17-Nov-08 nn0mulcl  nn0mulcli
17-Nov-08 nn0opth   nn0opthi
17-Nov-08 nn0opth2  nn0opth2i
17-Nov-08 nn0re     nn0rei
17-Nov-08 nncn      nncni
17-Nov-08 nneo      nneoi
17-Nov-08 nnesq     nnesqi
17-Nov-08 nngt0     nngt0i
17-Nov-08 nnlesq    nnlesqi
17-Nov-08 nnne0     nnne0i
17-Nov-08 nnnn0     nnnn0i
17-Nov-08 nnre      nnrei
17-Nov-08 nnsqcl    nnsqcli
17-Nov-08 nnsub     nnsubi
17-Nov-08 om2uz0    om2uz0i
17-Nov-08 om2uzf1o  om2uzf1oi
17-Nov-08 om2uziso  om2uzisoi
17-Nov-08 om2uzlt   om2uzlti
17-Nov-08 om2uzlt2  om2uzlt2i
17-Nov-08 om2uzran  om2uzrani
17-Nov-08 om2uzsuc  om2uzsuci
17-Nov-08 om2uzuz   om2uzuzi
17-Nov-08 peano2zd  peano2zdi
17-Nov-08 peano5nn  peano5nni
17-Nov-08 peano5uz  peano5uzi
17-Nov-08 peano5uzt peano5uzti
17-Nov-08 pm2.61ltle pm2.61ltlei
17-Nov-08 pncan3    pncan3i
17-Nov-08 pnncan    pnncani
17-Nov-08 posdif    posdifi
17-Nov-08 posex     posexi
17-Nov-08 prodge0   prodge0i
17-Nov-08 prodgt0   prodgt0i
17-Nov-08 readd     readdi
17-Nov-08 readdcl   readdcli
17-Nov-08 rec11     rec11i
17-Nov-08 rec11i    rec11ii
17-Nov-08 reccl     reccli
17-Nov-08 recclz    recclzi
17-Nov-08 reccnv    reccnvi
17-Nov-08 receu     receui
17-Nov-08 recex     recexi
17-Nov-08 recgt0    recgt0i
17-Nov-08 recgt0i   recgt0ii
17-Nov-08 recid     recidi
17-Nov-08 recidz    recidzi
17-Nov-08 recj      recji
17-Nov-08 recl      recli
17-Nov-08 recn      recni
17-Nov-08 recnd     recndi
17-Nov-08 recne0z   recne0zi
17-Nov-08 recrec    recreci
17-Nov-08 recvalz   recvalzi
17-Nov-08 redivcl   redivcli
17-Nov-08 redivclz  redivclzi
17-Nov-08 reef11    reef11i
17-Nov-08 reefcl    reefcli
17-Nov-08 reeftlclt reeftlclti
17-Nov-08 reim0b    reim0bi
17-Nov-08 releabs   releabsi
17-Nov-08 remul     remuli
17-Nov-08 remulcl   remulcli
17-Nov-08 reneg     renegi
17-Nov-08 renegcl   renegcli
17-Nov-08 replim    replimi
17-Nov-08 rereb     rerebi
17-Nov-08 rereccl   rereccli
17-Nov-08 rerecclz  rerecclzi
17-Nov-08 resqcl    resqcli
17-Nov-08 resubcl   resubcli
17-Nov-08 reuunineg reuunineg
17-Nov-08 seq00     seq00i
17-Nov-08 seq01     seq01i
17-Nov-08 seq0fn    seq0fni
17-Nov-08 seq0fval  seq0fvali
17-Nov-08 seq0p1    seq0p1i
17-Nov-08 seq0seqz  seq0seqzi
17-Nov-08 seq0valt  seq0valti
17-Nov-08 seq11     seq11i
17-Nov-08 seq1bnd   seq1bndi
17-Nov-08 seq1cl    seq1cli
17-Nov-08 seq1cl2   seq1cl2i
17-Nov-08 seq1f     seq1fi
17-Nov-08 seq1f2    seq1f2i
17-Nov-08 seq1fn    seq1fni
17-Nov-08 seq1m1    seq1m1i
17-Nov-08 seq1p1    seq1p1i
17-Nov-08 seq1res   seq1resi
17-Nov-08 seq1rn    seq1rni
17-Nov-08 seq1rn2   seq1rn2i
17-Nov-08 seq1rval  seq1rvali
17-Nov-08 seq1seq0  seq1seq0i
17-Nov-08 seq1seq02t seq1seq02ti
17-Nov-08 seq1seq0t seq1seq0ti
17-Nov-08 seq1seqz  seq1seqzi
17-Nov-08 seq1shftid seq1shftidi
17-Nov-08 seq1ub    seq1ubi
17-Nov-08 seq1val   seq1vali
17-Nov-08 seq1val2  seq1val2i
17-Nov-08 seqz1     seqz1i
17-Nov-08 seqzcl    seqzcli
17-Nov-08 seqzeq    seqzeqi
17-Nov-08 seqzfn    seqzfni
17-Nov-08 seqzfval  seqzfvali
17-Nov-08 seqzfval2 seqzfval2i
17-Nov-08 seqzfveq  seqzfveqi
17-Nov-08 seqzm1    seqzm1i
17-Nov-08 seqzp1    seqzp1i
17-Nov-08 seqzres   seqzresi
17-Nov-08 seqzres2  seqzres2i
17-Nov-08 seqzresval seqzresvali
17-Nov-08 seqzrn    seqzrni
17-Nov-08 seqzrn2   seqzrn2i
17-Nov-08 seqzval2t seqzval2ti
17-Nov-08 seqzvalt  seqzvalti
17-Nov-08 ser00     ser00i
17-Nov-08 ser0cj    ser0cji
17-Nov-08 ser0cl1   ser0cl1i
17-Nov-08 ser0clt   ser0clti
17-Nov-08 ser0f     ser0fi
17-Nov-08 ser0mulc  ser0mulci
17-Nov-08 ser0p1    ser0p1i
17-Nov-08 ser11     ser11i
17-Nov-08 ser1absdif ser1absdifi
17-Nov-08 ser1add   ser1addi
17-Nov-08 ser1add2  ser1add2i
17-Nov-08 ser1cl1   ser1cl1i
17-Nov-08 ser1cl2   ser1cl2i
17-Nov-08 ser1clt   ser1clti
17-Nov-08 ser1cmp   ser1cmpi
17-Nov-08 ser1cmp0  ser1cmp0i
17-Nov-08 ser1cmp2  ser1cmp2i
17-Nov-08 ser1const ser1consti
17-Nov-08 ser1f     ser1fi
17-Nov-08 ser1f0    ser1f0i
17-Nov-08 ser1f2    ser1f2i
17-Nov-08 ser1mono  ser1monoi
17-Nov-08 ser1mulc  ser1mulci
17-Nov-08 ser1p1    ser1p1i
17-Nov-08 ser1recl  ser1recli
17-Nov-08 ser1ref   ser1refi
17-Nov-08 ser1ser0  ser1ser0i
17-Nov-08 serz1p    serz1pi
17-Nov-08 serzcj    serzcji
17-Nov-08 serzcl1   serzcl1i
17-Nov-08 serzcl2t  serzcl2ti
17-Nov-08 serzclt   serzclti
17-Nov-08 serzcmp   serzcmpi
17-Nov-08 serzcmp0  serzcmp0i
17-Nov-08 serzf0    serzf0i
17-Nov-08 serzfsum  serzfsumi
17-Nov-08 serzim    serzimi
17-Nov-08 serzmulc  serzmulci
17-Nov-08 serzmulc1 serzmulc1i
17-Nov-08 serzre    serzrei
17-Nov-08 serzreclt serzreclti
17-Nov-08 serzref   serzrefi
17-Nov-08 serzsplit serzspliti
17-Nov-08 shftcan1t shftcan1ti
17-Nov-08 shftcan2t shftcan2ti
17-Nov-08 shftf     shftfi
17-Nov-08 shftfn    shftfni
17-Nov-08 shftfval  shftfvali
17-Nov-08 shftidt   shftidti
17-Nov-08 shftres   shftresi
17-Nov-08 shftresvalt shftresvalti
17-Nov-08 shftval2t shftval2ti
17-Nov-08 shftval3t shftval3ti
17-Nov-08 shftval4t shftval4ti
17-Nov-08 shftval5t shftval5ti
17-Nov-08 shftvalt  shftvalti
17-Nov-08 sinadd    sinaddi
17-Nov-08 sq11      sq11i
17-Nov-08 sqabsadd  sqabsaddi
17-Nov-08 sqabssub  sqabssubi
17-Nov-08 sqcl      sqcli
17-Nov-08 sqdiv     sqdivi
17-Nov-08 sqeq0     sqeq0i
17-Nov-08 sqeqor    sqeqori
17-Nov-08 sqge0     sqge0i
17-Nov-08 sqgt0     sqgt0i
17-Nov-08 sqmul     sqmuli
17-Nov-08 sqr11     sqr11i
17-Nov-08 sqrcl     sqrcli
17-Nov-08 sqreci    sqrecii
17-Nov-08 sqrge0    sqrge0i
17-Nov-08 sqrgt0    sqrgt0i
17-Nov-08 sqrgt0i   sqrgt0ii
17-Nov-08 sqrle     sqrlei
17-Nov-08 sqrlt     sqrlti
17-Nov-08 sqrmsq    sqrmsqi
17-Nov-08 sqrmsq2   sqrmsq2i
17-Nov-08 sqrmul    sqrmuli
17-Nov-08 sqrmuli   sqrmulii
17-Nov-08 sqrsq     sqrsqi
17-Nov-08 sqrth     sqrthi
17-Nov-08 sqsqr     sqsqri
17-Nov-08 sqval     sqvali
17-Nov-08 subadd    subaddi
17-Nov-08 subadd2   subadd2i
17-Nov-08 subaddri  subaddrii
17-Nov-08 subcan    subcani
17-Nov-08 subcan2   subcan2i
17-Nov-08 subcl     subcli
17-Nov-08 subdi     subdii
17-Nov-08 subdir    subdiri
17-Nov-08 subeq0    subeq0i
17-Nov-08 subge0    subge0i
17-Nov-08 subid     subidi
17-Nov-08 subid1    subid1i
17-Nov-08 subneg    subnegi
17-Nov-08 subsq     subsqi
17-Nov-08 subsq0    subsq0i
17-Nov-08 subsub23  subsub23i
17-Nov-08 sumsqne0  sumsqne0i
17-Nov-08 sup3i     sup3ii
17-Nov-08 suprcli   suprclii
17-Nov-08 suprleubi suprleubii
17-Nov-08 suprlubi  suprlubii
17-Nov-08 suprnubi  suprnubii
17-Nov-08 suprubi   suprubii
17-Nov-08 times2    times2i
17-Nov-08 uzinfm    uzinfmi
17-Nov-08 uzrdgfnuz uzrdgfnuzi
17-Nov-08 uzrdgini  uzrdginii
17-Nov-08 uzrdginip1 uzrdginip1i
17-Nov-08 uzrdgsuc  uzrdgsuci
17-Nov-08 uzrdgval  uzrdgvali
17-Nov-08 zre       zrei
17-Nov-08 abs3lem   abs3lemi
17-Nov-08 abs2difabs abs2difabsi
17-Nov-08 abs2dif   abs2difi
17-Nov-08 2basgent  2basgen
17-Nov-08 basgent   basgen
17-Nov-08 basgen2t  basgen2
17-Nov-08 tgss3t    tgss3
17-Nov-08 tgss2t    tgss2
17-Nov-08 tgsst     tgss
17-Nov-08 tgtop11t  tgtop11
17-Nov-08 bastopt   bastop
17-Nov-08 bastop    bastop1
17-Nov-08 tgidmt    tgidm
17-Nov-08 eltop3t   eltop3
17-Nov-08 eltop2t   eltop2
17-Nov-08 eltopt    eltop
17-Nov-08 tgtopt    tgtop
17-Nov-08 topbast   topbas
17-Nov-08 eltg3t    eltg3
17-Nov-08 tgval3t   tgval3
17-Nov-08 tgclt     tgcl
17-Nov-08 unitgt    unitg
17-Nov-08 bastgt    bastg
17-Nov-08 tg2t      tg2
17-Nov-08 tg1t      tg1
17-Nov-08 eltg2t    eltg2
17-Nov-08 eltgt     eltg
17-Nov-08 tgval2t   tgval2
17-Nov-08 tgvalt    tgval
17-Nov-08 basis2t   basis2
17-Nov-08 basis1t   basis1
17-Nov-08 0opnt     0opn
17-Nov-08 inopnt    inopn
17-Nov-08 iunopnt   iunopn
17-Nov-08 uniopnt   uniopn
17-Nov-08 uniopn    uniopn2
17-Nov-08 entrt     entr
17-Nov-08 entr4     entr4i
17-Nov-08 entr3     entr3i
17-Nov-08 entr2     entr2i
17-Nov-08 entr      entri
17-Nov-08 entri     entric
17-Nov-08 rdglimt   rdglim
17-Nov-08 onelpsst  onelpss
17-Nov-08 rdgsuct   rdgsuc
17-Nov-08 on0eqelt  on0eqel
17-Nov-08 onelsst   onelss
17-Nov-08 onsst     onss
17-Nov-08 rdglim    rdglimi
17-Nov-08 rdgsuc    rdgsuci
17-Nov-08 nnon      nnoni
17-Nov-08 onsucss   onsucssi
17-Nov-08 onun      onun2i
17-Nov-08 onssel    onsseli
17-Nov-08 onuninsuc onuninsuci
17-Nov-08 onuniorsuc onuniorsuci
17-Nov-08 onunisuc  onunisuci
17-Nov-08 onsuc     onsuci
17-Nov-08 onelun    oneluni
17-Nov-08 onelin    onelini
17-Nov-08 onssneli2 onssnel2i
17-Nov-08 onelss    onelssi
17-Nov-08 onss      onssi
17-Nov-08 onel      oneli
17-Nov-08 onirr     onirri
17-Nov-08 ontrc     ontrci
17-Nov-08 onord     onordi
17-Nov-08 ---       ---         The *tr inferences were changed to *tri,
17-Nov-08 ---       ---         for consistency with *tr*d
17-Nov-08 bitr      bitri
17-Nov-08 bitr2     bitr2i
17-Nov-08 bitr3     bitr3i
17-Nov-08 bitr4     bitr4i
17-Nov-08 3bitr     3bitri
17-Nov-08 3bitrr    3bitrri
17-Nov-08 3bitr2    3bitr2i
17-Nov-08 3bitr3    3bitr3i
17-Nov-08 3bitr4    3bitr4i
17-Nov-08 3imtr3    3imtr3i
17-Nov-08 3imtr4    3imtr4i
17-Nov-08 eqtr      eqtri
17-Nov-08 eqtr2     eqtr2i
17-Nov-08 eqtr3     eqtr3i
17-Nov-08 eqtr4     eqtr4i
17-Nov-08 3eqtr     3eqtri
17-Nov-08 3eqtrr    3eqtrri
17-Nov-08 3eqtr2    3eqtr2i
17-Nov-08 3eqtr3    3eqtr3i
17-Nov-08 3eqtr4    3eqtr4i
17-Nov-08 eq2tr     eq2tri
17-Nov-08 eqeltr    eqeltri
17-Nov-08 eqeltrr   eqeltrri
17-Nov-08 eleqtr    eleqtri
17-Nov-08 eleqtrr   eleqtrri
17-Nov-08 eqsstr    eqsstri
17-Nov-08 eqsstr3   eqsstr3i
17-Nov-08 sseqtr    sseqtri
17-Nov-08 sseqtr4   sseqtr4i
17-Nov-08 3sstr3    3sstr3i
17-Nov-08 3sstr4    3sstr4i
17-Nov-08 eqbrtr    eqbrtri
17-Nov-08 eqbrtrr   eqbrtrri
17-Nov-08 breqtr    breqtri
17-Nov-08 breqtrr   breqtrri
17-Nov-08 3brtr3    3brtr3i
17-Nov-08 3brtr4    3brtr4i
16-Nov-08 opabsb    opelopabsb
14-Nov-08 zfext2    axext3
14-Nov-08 axext     axext2
14-Nov-08 nega      notnot2
14-Nov-08 negai     notnotri
14-Nov-08 negb      notnot1
14-Nov-08 negbi     notnoti
14-Nov-08 negbii    notbii
14-Nov-08 negbid    notbid
14-Nov-08 pm4.13    notnot
14-Nov-08 pm4.11    notbi
11-Nov-08 divmul3t  [--same--]  rearranged antecedent; renamed variables
11-Nov-08 divmul2t  [--same--]  rearranged antecedent; renamed variables
11-Nov-08 divmult   [--same--]  rearranged antecedent; renamed variables
11-Nov-08 elqsi     [--same--]  changed E. x ( x e. A /\ ...  to E. x e. A ...
11-Nov-08 elqs      [--same--]  changed E. x ( x e. A /\ ...  to E. x e. A ...
 8-Nov-08 indistop  [--same--]  eliminated hypothesis A e. _V
 8-Nov-08 pri2      prid2
 8-Nov-08 pri1      prid1
 7-Nov-08 qdivclt   [--same--]  antecedent changed to use triple conjunction
 6-Nov-08 rcfpfil   [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 rcfpfillem6 [--same--] changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 rcfpfillem5 [--same--] changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 rcfpfillem4 [--same--] changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 rcfpfillem3 [--same--] changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 rcfpfillem2 [--same--] changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 rcfpfillem1 [--same--] changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fisub     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 filint2   [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 efilcp    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fgsb      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fipfil2   [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 sppfi     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fiv       [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 df-fi     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 0fin     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 ficli     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fiiu      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 abfi      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fine      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 infi1     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 spfi      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fctop     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 subbas2   [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 subbas    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 istps5    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 istps4    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 istop2g   [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 isfinite  [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 pwfi      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 pwfilem   [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 iunfi     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fofi      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fodomfib  [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 fodomfi   [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 abfii5    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Nov-08 abfii4    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
31-Sep-08 isfinite1 [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
31-Sep-08 domfi     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
31-Sep-08 unifi     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
31-Sep-08 abfii1    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
31-Sep-08 abfii2    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
31-Sep-08 abfii3    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
10-Sep-08 isfinite2 [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 9-Sep-08 fisucdom  [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 7-Sep-08 ominf     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Sep-08 onfin     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Sep-08 pssinf    {--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 6-Sep-08 divsubdirt [--same--] changed hyp. order
 3-Sep-08 php3      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 2-Sep-08 fiint     [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
 1-Sep-08 prfi      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
30-Aug-08 unfi      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
29-Aug-08 snfi      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
29-Aug-08 ssnnfi    [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
29-Aug-08 ssfi      [--same--]  changed "E. ... e. om ... ~~ ..." to "e. Fin"
24-Aug-08 mulcant   [--same--]  changed antecendent order; swapped var. names
24-Aug-08 mulcan2t  [--same--]  changed antecendent order; swapped var. names
24-Aug-08 mulcant2  [--same--]  changed hyp. order; swapped var. names
24-Aug-08 mulcan    [--same--]  changed hyp. order; swapped var. names
23-Aug-08 divcan4t  [--same--]  changed antecendent order; swapped var. names
23-Aug-08 divcan4z  [--same--]  changed hyp. order; swapped var. names
23-Aug-08 divcan3t  [--same--]  changed antecendent order; swapped var. names
23-Aug-08 divcan3z  [--same--]  changed hyp. order; swapped var. names
22-Aug-08 ssnn      ssnnfi
22-Aug-08 divcan4   [--same--]  changed hyp. order; swapped var. names
22-Aug-08 divcan3   [--same--]  changed hyp. order; swapped var. names
21-Aug-08 pm4.2i    biidd
21-Aug-08 divcan2t  [--same--]  changed antecendent order; swapped var. names
21-Aug-08 divcan2z  [--same--]  changed hyp. order; swapped var. names
20-Aug-08 divdirt   [--same--]  changed hyp. order
18-Aug-08 divcan2   [--same--]  changed hyp. order; swapped var. names
18-Aug-08 divcan1t  [--same--]  changed antecendent order; swapped var. names
18-Aug-08 divcan1z  [--same--]  changed hyp. order; swapped var. names
18-Aug-08 divcan1   [--same--]  changed hyp. order; swapped var. names
17-Aug-08 ltmuldiv2t [--same--] changed antecedent grouping
17-Aug-08 ltdivmult [--same--]  changed antecedent grouping
17-Aug-08 ledivmult [--same--]  changed antecedent grouping
17-Aug-08 ltdivmul2t [--same--] changed antecedent grouping
17-Aug-08 ledivmul2t [--same--] changed antecedent grouping
17-Aug-08 lemuldivt [--same--]  changed antecedent grouping
17-Aug-08 lemuldiv2t [--same--] changed antecedent grouping
16-Aug-08 ltmuldivt [--same--]  changed antecedent grouping
15-Aug-08 bii       dfbi1
15-Aug-08 biigb     dfbi1gb
15-Aug-08 bi        dfbi2
15-Aug-08 dfbi      dfbi3
14-Aug-08 lediv1t   [--same--]  changed antecedent grouping
14-Aug-08 ltdiv1t   [--same--]  changed antecedent grouping
10-Jul-08 expne0t   [--same--]  swapped biconditional
10-Jul-08 sq0t      sqeq0t
10-Jul-08 sq00      sqeq0
 7-Jul-08 syl3dan3  syld3an3
 7-Jul-08 syl3dan2  syld3an2
31-May-08 isnvi     [--same--]  eliminated hypotheses G e. V, S e. _V
31-May-08 isnvg     ---         obsolete; use isnv
31-May-08 isvcg     ---         obsolete; use isvc
31-May-08 ideq      [--same--]  eliminated hypothesis A e. _V
31-May-08 ideqg     [--same--]  eliminated first antecedent A e. C
28-May-08 opelxpex  ---         obsolete; use opelxp1
22-May-08 ax9a      ax9
22-May-08 ax9       ax9o
21-May-08 ax6-2     ax6
21-May-08 ax6-3     ax6o
21-May-08 ax-6      ax-6o
21-May-08 ax-5      ax-5o
17-May-08 ax-10     ax-10o
16-May-08 er2       dfer2
16-May-08 er2       dfer2
16-May-08 sb7       dfsb7
13-May-08 cla4e2v   cla42ev
13-May-08 cla4e2gv  cla42egv
12-May-08 a4w1      a4eiv
12-May-08 a4w       a4imev
12-May-08 a4c1      a4imed
12-May-08 a4c       a4ime
12-May-08 a4b1      a4v
12-May-08 a4b       a4imv
12-May-08 a4at      a4imt
12-May-08 a4a       a4im
11-May-08 sbea4     a4sbe
11-May-08 sbia4     a4sbim
11-May-08 sbba4     a4sbbi
 6-May-08 inf4      axinf2
 6-May-08 minfnre   mnfnre
27-Apr-08 sb6y      sb6f
27-Apr-08 sb5y      sb5f
17-Apr-08 sbn2      ---         obsolete; use sbn
17-Apr-08 sbn1      ---         obsolete; use sbn
 9-Apr-08 isvci     [--same--]  weakened hyp from G : ... to dom G = ...
 9-Apr-08 isabli    [--same--]  weakened hyp from G : ... to dom G = ...
 2-Apr-08 19.2      [--same--]  generalized to use 2 set variables
30-Mar-08 grprn     [--same--]  weakened hyp from G : ... to dom G = ...
11-Mar-08 absefimt  absefit
11-Mar-08 axcnre    [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 cnegexlem2 [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 cnegext   [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 recextlem1 [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 recextlem2 [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 recext    [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 crulem    [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 cru       [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 crut      [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 crne0     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 crmul     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 crrecz    [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 creur     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 creui     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 rimul     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 df-re     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 df-im     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 revalt    [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 imvalt    [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 replimt   [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 df-cj     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 cjvalt    [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 replim    [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 crret     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 crimt     [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 crre      [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 crim      [--same--]  changed 'x. i' to 'i x.'
11-Mar-08 efit4pt   efi4pt      changed 'x. i' to 'i x.'
10-Mar-08 fabex     [--same--]  added 3rd hypothesis
 6-Mar-08 pm2.36    [--same--]  corrected to match Principia Mathematica
 6-Mar-08 pm2.37    [--same--]  corrected to match Principia Mathematica
 6-Mar-08 pm2.38    [--same--]  corrected to match Principia Mathematica
 2-Mar-08 csbiet    csbiegft
 2-Mar-08 csbie2g   csbie2t
 2-Mar-08 vsbcint   sbhyp
 2-Mar-08 cbvsbcv   cbvralsv
 1-Mar-08 sbcrex    sbcrexg
 1-Mar-08 sbcral    sbcralg
 1-Mar-08 19.23g    19.23t
 1-Mar-08 19.21g    19.21t
 1-Mar-08 minusex   negex
 1-Mar-08 negext    cnegext
 1-Mar-08 negex     cnegex
29-Feb-08 hbneq     hbne
29-Feb-08 hbne      hbn
29-Feb-08 csbiet    csbiegft
29-Feb-08 sbciet    sbciegft
29-Feb-08 elabt     elabgt
29-Feb-08 vtoclefg  vtoclegft
23-Feb-08 sqdif0    subsq0
23-Feb-08 binom2a   ---         obsolete; use subsq
12-Feb-08 cnhl      [--same--]  added hypothesis to assign vector space to var
 9-Feb-08 oneirr    onirr
 9-Feb-08 ordeirr   ordirr
 9-Feb-08 eirr      elirr
 9-Feb-08 eirrv     elirrv
29-Jan-08 oibabs    [--same--]  swapped sides of biconditional
24-Jan-08 cos2t     ---         obsolete; use cos2tt
20-Jan-08 ffvrni    ffvelrni
20-Jan-08 ffvrn     ffvelrn
20-Jan-08 fnfvrn    fnfvelrn
20-Jan-08 fvrn      fvelrn
20-Jan-08 fvelrn    fvelrnb
18-Jan-08 arch      [--same--]  changed x to n, changing $f hypothesis order
18-Jan-08 cos1lem4  8th4div3
18-Jan-08 eftlex    ---         obsolete; use eftlext
18-Jan-08 sin2t     ---         obsolete; use sin2tt
15-Jan-08 explt1t   expord2t
15-Jan-08 eft0vallem eft0val
15-Jan-08 effsumlelem ---       obsolete; use reeftclt
15-Jan-08 eftvallem eftval
15-Jan-08 efpartex  eftlex
15-Jan-08 efcltlem4 efseq0ex
15-Jan-08 efcltlem2a ef0lem
15-Jan-08 dfef2lem  dfef2
15-Jan-08 efcltlem3 efseq1ex
15-Jan-08 eftcltlem eftclt
15-Jan-08 eftabslem eftabs
12-Jan-08 rgen2xxx  rgen2a
12-Jan-08 rgen2a    rgen2
12-Jan-08 rgen2     rgen2xxx
12-Jan-08 cnbn      [--same--]  added hypothesis to assign vector space to var
12-Jan-08 cnph      [--same--]  added hypothesis to assign vector space to var
12-Jan-08 cnims     [--same--]  reorganized hypotheses and conclusion
14-Jan-08 rgen3     [--same--]  generalized for 3 different class variables
12-Jan-08 cnnv      [--same--]  added hypothesis to assign vector space to var
10-Jan-08 zneo      [--same--]  changed -. ... = to =/=
 3-Jan-08 ax7-467   ax467to7
 3-Jan-08 ax6-467   ax467to6
 3-Jan-08 ax4-467   ax467to4
 3-Jan-08 ax6-67    ax67to6
 3-Jan-08 ax7-67    ax67to7
 3-Jan-08 ax4-46    ax46to4
 3-Jan-08 ax5-46    ax46to5
29-Dec-07 eftvallem [--same--]  added hypothesis
22-Dec-07 zfnuleu   [--same--]  added $e hypothesis to remove ax-nul dependency
 8-Dec-07 supxrre2  [--same--]  changed -. ... = to =/=
23-Nov-07 sub4      addsub4
23-Nov-07 sub4t     addsub4t
17-Nov-07 climres   [--same--]  generalized antecedent from A e. CC to A e. B
12-Nov-07 climle    climcmp
11-Nov-07 eqneqi    necon3bii
11-Nov-07 eqneqd    necon3bid
10-Nov-07 ser0cj    [--same--]  weakened hypotheses
 9-Nov-07 ser1cj    ---         obsolete; derive from serzcj (as in ser0cj)
 9-Nov-07 ser0re    ---         obsolete; derive from serzre (as in ser0cj)
 9-Nov-07 ser1re    ---         obsolete; derive from serzre (as in ser0cj)
 8-Nov-07 mp3dan    mp3dan23
23-Oct-07 pm3.27bd  simprbi
23-Oct-07 pm3.26bd  simplbi
16-Oct-07 expbndt   expubndt
16-Oct-07 expge1t   [--same--]  strengthened from N e. NN to N e. NN0
12-Oct-07 kmlem15   [--same--]  changed -. ... = to =/=
12-Oct-07 kmlem14   [--same--]  changed -. ... = to =/=
12-Oct-07 kmlem13   [--same--]  changed -. ... = to =/=
12-Oct-07 kmlem10   [--same--]  changed -. ... = to =/=
12-Oct-07 kmlem9    [--same--]  changed -. ... = to =/=
12-Oct-07 kmlem7    [--same--]  changed -. ... = to =/=
12-Oct-07 kmlem5    [--same--]  changed -. ... = to =/=
12-Oct-07 kmlem4    [--same--]  changed -. ... = to =/=
12-Oct-07 kmlem3    [--same--]  changed -. ... = to =/=
 5-Oct-07 1open     topopn
 5-Oct-07 1clsd     topcld
 3-Oct-07 intss3    ntrss3
 2-Oct-07 isopen3   isopn3
 2-Oct-07 isopen2   isopn2
 2-Oct-07 cmclsopen cmclsopn
 2-Oct-07 snclsd    sncld
 2-Oct-07 clsdlp    cldlp
 2-Oct-07 isclsd3   iscld3
 2-Oct-07 cmntrclsd cmntrcld
 2-Oct-07 clsclsd   clscld
 2-Oct-07 clsdcls   cldcls
 2-Oct-07 unclsd    uncld
 2-Oct-07 intclsd   intcld
 2-Oct-07 iinclsd   iincld
 2-Oct-07 0clsd     0cld
 2-Oct-07 openclsd  opncld
 2-Oct-07 clsdopen  cldopn
 2-Oct-07 clsdss    cldss
 2-Oct-07 isclsd2   iscld2
 2-Oct-07 isclsd    iscld
 2-Oct-07 clsdval   cldval
 2-Oct-07 df-clsd   df-cld
 2-Oct-07 isopn2    isopn4
28-Sep-07 ---       ---         changed math symbol from "floor" to "|_"
26-Sep-07 ser0cl    ser0cl1
26-Sep-07 ser1cl    ser1cl1
25-Sep-07 ser1re2   ser1re
25-Sep-07 ser1re    ser1ref
23-Sep-07 df-fac    [--same--]  swapped arguments of union
23-Sep-07 seqzrnx   seqzrn
23-Sep-07 seqzrn    seqzrn2
23-Sep-07 seqzrn2   seqzrnx
23-Sep-07 seq1rnx   seq1rn
23-Sep-07 seq1rn    seq1rn2
23-Sep-07 seq1rn2   seq1rnx
17-Sep-07 pm2.21nd  pm2.24d
17-Sep-07 pm2.21ni  pm2.24i
16-Sep-07 dvelimf2  dvelimfALT
 8-Sep-07 lemul2it  [--same--]  rearranged antecedent
 8-Sep-07 lemul1it  [--same--]  rearranged antecedent
 7-Sep-07 0vval     0vfval
 4-Sep-07 ---       ---         Many changes after df-ms, described in the
                                  4-Sep-2007 entry of
                                  us.metamath.org/mpegif/mmnotes.txt
 4-Sep-07 elssab    ---         obsolete; use elssabg
 4-Sep-07 nvc       nvvc
 4-Sep-07 ---       ---         changed math symbol from "Met" to "MetSp"
 4-Sep-07 ---       ---         changed math symbol from "CMet" to "CMetSp"
25-Aug-07 fopabco   fopabcos
21-Aug-07 xrltnet   [--same--]  changed -. A = B to B =/= A; triple conjunction
21-Aug-07 lttri2    [--same--]  changed -. A = B to A =/= B
21-Aug-07 lttri2t   [--same--]  changed -. A = B to A =/= B
15-Aug-07 sbccsbg   sbccsb2g
11-Aug-07 recdivt   [--same--]  rearranged antecedent
 9-Aug-07 funopabex2g opabex2g
 9-Aug-07 funopabex2 opabex2
 9-Aug-07 funopabex opabex
 9-Aug-07 cnco      [--same--]  swapped 2nd & 3rd args in 1st triple conj
 6-Aug-07 ---       ---         changed "ncv" to "nv" in the labels of:
                                  cncv df-ncv ncvss ncvrel ncvop ncvvop
                                  isncvg isncvi ncvi ncvv ncvgcl
                                  ncvscl ncvf ncvcl ncvcli ncvdm ncvs
                                  ncvm1 ncvdif ncvpi ncvz0 ncvz ncvtri
                                  ncvabs ncvge0 cnncv cnncv0 elimncvu
                                  ncvnd phncv bnncv hlncv hilncv
 4-Aug-07 subval    ---         obsolete; use subvalt
31-Jul-07 divge0t   [--same--]  rearranged antecedent
31-Jul-07 divgt0t   [--same--]  rearranged antecedent
31-Jul-07 ltne      [--same--]  changed -. A = B to B =/= A
31-Jul-07 ltnet     [--same--]  changed -. A = B to B =/= A; triple conjunction
31-Jul-07 ltlen     [--same--]  changed -. A = B to B =/= A
31-Jul-07 ltlent    [--same--]  changed -. A = B to B =/= A
22-Jul-07 xrleltnet [--same--]  changed -. A = B to B =/= A
20-Jul-07 nngt1ne1t [--same--]  changed -. A = 1 to A =/= 1
18-Jul-07 leltnet   [--same--]  changed -. A = B to B =/= A
15-Ju1-07 zornx     zorn
15-Ju1-07 zorn      zorn2
15-Ju1-07 zorn2     zornx
18-Jun-07 caucvglem2 [--same--]  changed -. S = (/) to S =/= (/)
17-Jun-07 seq1ublem [--same--]  changed -. ... = (/) to =/= (/)
17-Jun-07 suppr     supexpr
17-Jun-07 ruclem33  [--same--]  changed -. ... = (/) to =/= (/)
16-Jun-07 ltrec1t   [--same--]  rearranged antecedent
15-Jun-07 lerec2t   [--same--]  rearranged antecedent
 3-Jun-07 nordeq    [--same--]  changed -. A = B to A =/= B
 3-Jun-07 xpsndisj  [--same--]  changed -. A = B to A =/= B
 2-Jun-07 peano3    [--same--]  changed -. A = (/) to A =/= (/)
 2-Jun-07 disjsn2   [--same--]  changed -. A = B to A =/= B
 2-Jun-07 fun2ssres [--same--]  antecedent changed to use triple conjunction
 2-Jun-07 onelpsst  [--same--]  changed -. A = B to A =/= B
 1-Jun-07 ordelssne [--same--]  changed -. A = B to A =/= B
 1-Jun-07 suprleubi [--same--]  changed -. A = (/) to A =/= (/)
31-May-07 suprnubi  [--same--]  changed -. A = (/) to A =/= (/)
30-Mar-07 onssmin   [--same--]  changed -. A = (/) to A =/= (/)
29-May-07 suprlub   [--same--]  changed -. A = (/) to A =/= (/)
29-May-07 funssfv   [--same--]  antecedent changed to use triple conjunction
29-May-07 limuni3   [--same--]  changed -. A = (/) to A =/= (/)
29-May-07 ordge1n0  [--same--]  changed -. A = (/) to A =/= (/)
28-May-07 onmindif2 [--same--]  changed -. A = (/) to A =/= (/)
28-May-07 suprleub  [--same--]  changed -. A = (/) to A =/= (/)
28-May-07 tz7.7     [--same--]  changed -. B = A to B =/= A
27-May-07 nnullss   [--same--]  changed -. ... = (/) to =/= (/)
27-May-07 supxrre2  [--same--]  changed -. A = (/) to A =/= (/)
27-May-07 fodomfib  [--same--]  changed -. A = (/) to A =/= (/)
26-May-07 supxrre1  [--same--]  changed -. A = (/) to A =/= (/)
24-May-07 supxrgtmnf [--same--]  changed -. A = (/) to A =/= (/)
23-May-07 ltmsqt    ---         obsolete; use msqgt0t
23-May-07 msqgt0    [--same--]  changed -. A = (/) to A =/= (/)
22-May-07 supxrbnd  [--same--]  changed -. A = (/) to A =/= (/)
21-May-07 suprnub   [--same--]  changed -. A = (/) to A =/= (/)
21-May-07 19.3r     ---         obsolete; use 19.3
21-May-07 19.9rv    ---         obsolete; use 19.9v
20-May-07 19.9r     ---         obsolete; use 19.9
17-May-07 iunn0     [--same--]  changed -. ... = (/) to =/= (/)
17-May-07 iinon     [--same--]  changed -. A = (/) to A =/= (/)
17-May-07 map0      [--same--]  changed -. B = (/) to B =/= (/)
16-May-07 infmrcl   [--same--]  changed -. A = (/) to A =/= (/)
16-May-07 suprub    [--same--]  changed -. A = (/) to A =/= (/)
16-May-07 suprcli   [--same--]  changed -. A = (/) to A =/= (/)
16-May-07 suprubi   [--same--]  changed -. A = (/) to A =/= (/)
16-May-07 suprlubi  [--same--]  changed -. A = (/) to A =/= (/)
14-May-07 sup3i     [--same--]  changed -. A = (/) to A =/= (/)
13-May-07 kmlemxx   kmlem8      changed -. ... = (/) to =/= (/)
13-May-07 kmlem8    kmlem9
13-May-07 kmlem9    kmlem10
13-May-07 kmlem10   kmlem11
13-May-07 kmlem11   kmlem12     changed -. ... = to =/=
13-May-07 kmlem12   kmlem13     changed -. ... = to =/=
13-May-07 kmlem13   kmlemxx
13-May-07 supxrre   [--same--]  changed -. A = (/) to A =/= (/)
13-May-07 infmsup   [--same--]  changed -. A = (/) to A =/= (/)
13-May-07 suprcl    [--same--]  changed -. A = (/) to A =/= (/)
12-May-07 kmlem1    [--same--]  changed -. ... = to =/=
12-May-07 kmlem3    [--same--]  changed -. ... = to =/=
12-May-07 kmlem6    [--same--]  changed -. ... = to =/=
12-May-07 kmlem7    [--same--]  changed -. ... = to =/=
11-May-07 infm3     [--same--]  changed -. A = (/) to A =/= (/)
11-May-07 sup3      [--same--]  changed -. A = (/) to A =/= (/)
10-May-07 oneqmin   [--same--]  changed -. B = (/) to B =/= (/)
10-May-07 infmssuzcl [--same--]  changed -. S = (/) to S =/= (/)
 5-May-07 xpexr2    [--same--]  changed -. ... = (/) to =/= (/)
 5-May-07 tz7.49c   [--same--]  changed -. ... = to =/=
 4-May-07 tz7.49    [--same--]  changed -. ... = to =/=
 4-May-07 funimass2 [--same--]  conjoined antecedents in hypothesis
 3-May-07 ac4c      [--same--]  changed -. x = (/) to x =/= (/)
30-Apr-07 aceq6b    [--same--]  changed -. z = (/) to z =/= (/)
30-Apr-07 disjpss   [--same--]  changed -. B = (/) to B =/= (/)
30-Apr-07 infxpidmlem10 [--same--]  changed -. g = (/) to g =/= (/)
30-Apr-07 1ne0      [--same--]  changed -. 1o = (/) to 1o =/= (/)
30-Apr-07 ac5b      [--same--]  changed -. x = (/) to x =/= (/)
30-Apr-07 aceq6a    [--same--]  changed -. z = (/) to z =/= (/)
30-Apr-07 on0eln0   [--same--]  changed -. A = (/) to A =/= (/)
28-Apr-07 tz7.2     [--same--]  changed -. B = A to B =/= A; triple conjunction
25-Apr-07 ac5       [--same--]  changed -. x = (/) to x =/= (/)
23-Apr-07 ac4       [--same--]  changed -. z = (/) to z =/= (/)
22-Apr-07 ac8       [--same--]  changed -. ... = to =/=
22-Apr-07 uzwo2     [--same--]  changed -. S = (/) to S =/= (/)
21-Apr-07 aceq5     [--same--]  changed -. ... = to =/=
21-Apr-07 epfrc     [--same--]  -. B = (/) to B =/= (/); triple conjunction
20-Apr-07 dfepfr    [--same--]  changed -. x = (/) to x =/= (/)
19-Apr-07 xpnz      [--same--]  changed -. ... = (/) to =/= (/)
18-Apr-07 ltexprlem1 [--same--]  changed -. C = (/) to C =/= (/)
17-Apr-07 uzwo      [--same--]  changed -. S = (/) to S =/= (/)
17-Apr-07 aceq4     [--same--]  changed -. z = (/) to z =/= (/)
17-Apr-07 prn0      [--same--]  changed -. A = (/) to A =/= (/)
15-Apr-07 elni      [--same--]  changed -. A = (/) to A =/= (/)
14-Apr-07 aceq3lem  [--same--]  changed -. z = (/) to z =/= (/)
14-Apr-07 aceq3     [--same--]  changed -. z = (/) to z =/= (/)
13-Apr-07 tpnz      [--same--]  changed -. ... = (/) to =/= (/)
13-Apr-07 0nep0     [--same--]  changed -. (/) = { (/) } to (/) =/= { (/) }
12-Apr-07 1cn       ax1cn
12-Apr-07 ax1re     1re
11-Apr-07 zfreg     [--same--]  changed -. A = (/) to A =/= (/)
11-Apr-07 zfreg2    [--same--]  changed -. A = (/) to A =/= (/)
11-Apr-07 inf1      [--same--]  changed -. x = (/) to x =/= (/)
11-Apr-07 inf2      [--same--]  changed -. x = (/) to x =/= (/)
11-Apr-07 zorn2lem6  [--same--]  changed -. H = (/) to H =/= (/)
11-Apr-07 zorn2lem5  [--same--]  changed -. H = (/) to H =/= (/)
11-Apr-07 zorn2lem3  [--same--]  changed -. D = (/) to D =/= (/)
11-Apr-07 zorn2lem2  [--same--]  changed -. D = (/) to D =/= (/)
11-Apr-07 zorn2lem1  [--same--]  changed -. D = (/) to D =/= (/)
11-Apr-07 inf3lem2  [--same--]  changed -. ... = to =/=
11-Apr-07 inf3lem3  [--same--]  changed -. ... = to =/=
11-Apr-07 inf3lem4  [--same--]  changed -. -. x = (/) to x =/= (/)
11-Apr-07 inf3lem5  [--same--]  changed -. -. x = (/) to x =/= (/)
11-Apr-07 inf3lem6  [--same--]  changed -. -. x = (/) to x =/= (/)
11-Apr-07 inf3lem7  [--same--]  changed -. -. x = (/) to x =/= (/)
11-Apr-07 inf3      [--same--]  changed -. -. x = (/) to x =/= (/)
10-Apr-07 htalem    [--same--]  changed -. A = (/) to A =/= (/)
 9-Apr-07 ac3       [--same--]  changed -. z = (/) to z =/= (/)
 9-Apr-07 rnxp      [--same--]  changed -. A = (/) to A =/= (/)
 7-Apr-07 aceq2     [--same--]  changed -. z = (/) to z =/= (/)
 6-Apr-07 tz6.12i   [--same--]  changed -. B = (/) to B =/= (/)
 6-Apr-07 scott0s   [--same--]  changed -. .. = (/) to =/= { (/) }
 6-Apr-07 dmxp      [--same--]  changed -. A = (/) to A =/= (/)
 6-Apr-07 nnsuc     [--same--]  changed -. A = (/) to A =/= (/)
 5-Apr-07 onne0     [--same--]  changed -. On = (/) to On =/= (/)
 5-Apr-07 ord0eln0  [--same--]  changed -. A = (/) to A =/= (/)
 5-Apr-07 wereu     [--same--]  -. B = (/) to B =/= (/); triple conjunction
 3-Apr-07 aceq5lem5 [--same--]  changed -. u = (/) to u =/= (/)
 3-Apr-07 aceq5lem4 [--same--]  changed -. u = (/) to u =/= (/)
 3-Apr-07 aceq5lem3 [--same--]  changed -. u = (/) to u =/= (/)
 3-Apr-07 aceq5lem2 [--same--]  changed -. u = (/) to u =/= (/)
 3-Apr-07 pssdifn0  [--same--]  changed -. ... = to =/=
 3-Apr-07 fri       [--same--]  changed -. ... = (/) to ... =/= (/)
 2-Apr-07 cplem1    [--same--]  changed -. ... = (/) to =/= (/)
 2-Apr-07 cplem2    [--same--]  changed -. ... = (/) to =/= (/)
 2-Apr-07 0pss      [--same--]  changed -. A = (/) to A =/= (/)
 2-Apr-07 inelcm    [--same--]  changed -. ... = (/) to =/= (/)
 2-Apr-07 snnz      [--same--]  changed -. A = (/) to A =/= (/)
 2-Apr-07 inf0      [--same--]  changed conclusion to match ax-inf exactly
 2-Apr-07 n0f       ---         obsolete; use n0f
26-Mar-07 df-lim    [--same--]  changed -. A = (/) to A =/= (/)
26-Mar-07 pwen      [--same--]  eliminated redundant hypotheses
26-Mar-07 ssundif   undif
23-Mar-07 fo2       dffo2
23-Mar-07 fofv      dffo3
22-Mar-07 fnbr      [--same--]  eliminated redundant hypotheses
22-Mar-07 fnop      [--same--]  eliminated redundant hypotheses
21-Mar-07 kardex    [--same--]  eliminated redundant hypothesis
21-Mar-07 qsid      [--same--]  eliminated redundant hypothesis
21-Mar-07 0nelqs    [--same--]  eliminated redundant hypothesis
21-Mar-07 brecop2   [--same--]  eliminated redundant hypothesis
21-Mar-07 ecelqsdm  [--same--]  eliminated redundant hypothesis
18-Mar-07 map0b     [--same--]  changed -. A = (/) to A =/= (/)
17-Mar-07 oninton   [--same--]  changed -. A = (/) to A =/= (/)
17-Mar-07 wefrc     [--same--]  -. B = (/) to B =/= (/); triple conjunction
17-Mar-07 onint     [--same--]  changed -. A = (/) to A =/= (/)
17-Mar-07 tz7.5     [--same--]  -. B = (/) to B =/= (/); triple conjunction
17-Mar-07 fiint     [--same--]  changed -. x = (/) to x =/= (/)
16-Mar-07 ishlg     [--same--]  changed hypothesis from X = dom N to X = ran G
16-Mar-07 unitopt   ---         obsolete; use topopn
16-Mar-07 peano3nn0 nn0p1nnt
15-Mar-07 intex     [--same--]  changed -. A = (/) to A =/= (/)
 4-Mar-07 opthreg   [--same--]  added converse:  ->  to  <->
15-Feb-07 qbtwnre   [--same--]  antecedent changed to use triple conjunction
13-Feb-07 rcla42ev  [--same--]  antecedent changed to use triple conjunction
10-Feb-07 fodomb    [--same--]  changed -. A = (/) to A =/= (/)
 7-Feb-07 rabbidv   [--same--]  conjoined antecedents in hypothesis
 5-Feb-07 equidALT  equid1
 5-Feb-07 ax-11     ax-11o
 2-Feb-07 ax11a     ax11v
 1-Feb-07 frc       [--same--]  -. = (/) to =/= (/); conjoined antecedents
31-Jan-07 itimesi   ixi
31-Jan-07 isqm1     i2
30-Jan-07 dffr2     [--same--]  changed -. ... = (/) to ... =/= (/)
30-Jan-07 df-fr     [--same--]  changed -. ... = (/) to ... =/= (/)
30-Jan-07 f1oeng    [--same--]  conjoined antecedents
29-Jan-07 2sumeq2d  ---         obsolete; use 2sumeq2dv
29-Jan-07 sumeq12d  ---         obsolete; use sumeq12dv
29-Jan-07 sumeq12rd ---         obsolete; use sumeq12rdv
29-Jan-07 eval      [--same--]  ( 1 ^ k ) changed to 1
22-Jan-07 ax11el    [--same--]  generalized with less restrictive variables
18-Jan-07 climcvgc1 ---         obsolete; use clmi1
18-Jan-07 climcvg1  ---         obsolete; use clmi2
18-Jan-07 clim1     ---         obsolete; use clm2
18-Jan-07 clim1a    ---         obsolete; use clm3
18-Jan-07 clim2a    ---         obsolete; use clm2
18-Jan-07 clim2     ---         obsolete; use clm4
18-Jan-07 climcvg2  ---         obsolete; use clmi2
18-Jan-07 climcvg2z ---         obsolete; use clmi2
18-Jan-07 climcvgc2z ---        obsolete; use clmi1
18-Jan-07 climcvg2zb ---        obsolete; use clmi2
18-Jan-07 clim2az   ---         obsolete; use clm3
18-Jan-07 clim3az   ---         obsolete; use clm3
18-Jan-07 clim3a    ---         obsolete; use clm3
18-Jan-07 clim3     ---         obsolete; use clm4
18-Jan-07 clim3b    ---         obsolete; use clm2
18-Jan-07 climcvg3  ---         obsolete; use clmi2
18-Jan-07 climcvg3z ---         obsolete; use clmi2
18-Jan-07 clim4a    ---         obsolete; use clm3
18-Jan-07 clim4     ---         obsolete; use clm4
18-Jan-07 climcvg4  ---         obsolete; use clmi2
18-Jan-07 climcvgc4z ---        obsolete; use clmi1
18-Jan-07 climcvg4z ---         obsolete; use clmi2
18-Jan-07 clim0cvg4z ---        obsolete; use clm0i
18-Jan-07 climcvgc5z ---        obsolete; use clmi1
18-Jan-07 climcvg5z ---         obsolete; use clmi2
18-Jan-07 clim0cvg5z ---        obsolete; use clm0i
18-Jan-07 climnn0   ---         obsolete; use clm4
18-Jan-07 climnn    ---         obsolete; use clm4
18-Jan-07 clim0nn   ---         obsolete; use clm0
18-Jan-07 climcvgnn ---         obsolete; use clmi2
18-Jan-07 climcvgnn0 ---        obsolete; use clmi2
18-Jan-07 clim0cvgnn0 ---       obsolete; use clm0i
18-Jan-07 climcvg2nn0 ---       obsolete; use clmi2
18-Jan-07 clim0cvg2nn0 ---      obsolete; use clm0i
18-Jan-07 climnn0le ---         obsolete; use clm4le
18-Jan-07 clim0nn0le ---        obsolete; use clm4le and clm0
16-Jan-07 abn0      [--same--]  changed -. ... = (/) to ... =/= (/)
16-Jan-07 rabn0     [--same--]  changed -. ... = (/) to ... =/= (/)
16-Jan-07 nsuceq0   [--same--]  changed -. ... = (/) to ... =/= (/)
16-Jan-07 iin0      [--same--]  changed -. A = (/) to A =/= (/)
16-Jan-07 fint      [--same--]  changed -. B = (/) to B =/= (/)
14-Jan-07 clim3z    clm4at
12-Jan-07 climconst [--same--]  made M e. ZZ a hypothesis instead of antecedent
11-Jan-07 climres2  ---         obsolete; use climres
 4-Jan-07 iunconst  [--same--]  changed -. A = (/) to A =/= (/)
21-Dec-06 intssuni2 [--same--]  changed -. A = (/) to A =/= (/)
21-Dec-06 intssuni  [--same--]  changed -. A = (/) to A =/= (/)
21-Dec-06 prer2     preqr2
20-Dec-06 ccms      cnms
20-Dec-06 ccims     cnims
20-Dec-06 ccmsval   cnimsval
18-Dec-06 cvgannn   ---         obsolete; use cvganuz
18-Dec-06 cvgannn0  ---         obsolete; use cvganuz
14-Dec-06 cleqreli  eqrelriv
14-Dec-06 cleqrel   eqrel
12-Dec-06 rnco      rncoss
12-Dec-06 dmco      dmcoss
 5-Dec-06 r19.2z    [--same--]  -. A = (/) to A =/= (/); conjoined antecendents
24-Nov-06 infn0     [--same--]  changed -. A = (/) to A =/= (/)
24-Nov-06 0sdom     [--same--]  changed -. A = (/) to A =/= (/)
24-Nov-06 0sdomg    [--same--]  changed -. A = (/) to A =/= (/)
24-Nov-06 infxpabs  [--same--]  -. B = (/) to B =/= (/); use w3a for antec.
24-Nov-06 xpdom3    [--same--]  changed antecedent from -. B = (/) to B =/= (/)
14-Nov-06 zfnul     axnul
14-Nov-06 zfaus     axsep
28-Oct-06 inv       inv1
25-Oct-06 orcana    ---         obsolete; use pm5.6
10-Oct-06 oprec     [--same--]  changed order of $f hypotheses
10-Oct-06 ecoprdi   [--same--]  changed order of $f hypotheses
10-Oct-06 ecoprass  [--same--]  changed order of $f hypotheses
 9-Oct-06 unisseq   ---         obsolete; use unimax
 8-Oct-06 notzfaus  [--same--]  more meaningful first hypothesis
 8-Oct-06 intmin    [--same--]  swapped arguments of = sign
 8-Oct-06 intmin2   [--same--]  swapped arguments of = sign
 5-Oct-06 expcant   [--same--]  generalized antecedent from e. NN to e. NN0
 5-Oct-06 expsubt   [--same--]  generalized antecedent from e. NN to e. NN0
 5-Oct-06 divexpt   [--same--]  generalized antecedent from e. NN to e. NN0
 5-Oct-06 expwordit [--same--]  generalized antecedent from e. NN to e. NN0
 5-Oct-06 explt1t   [--same--]  generalized antecedent from e. NN to e. NN0
 5-Oct-06 recexpt   [--same--]  generalized antecedent from e. NN to e. NN0
 5-Oct-06 expordt   [--same--]  generalized antecedent from e. NN to e. NN0
 5-Oct-06 iineq2dv  [--same--]  conjoined antecedents in hypothesis
 5-Oct-06 iuneq2dv  [--same--]  conjoined antecedents in hypothesis
 5-Oct-06 r19.9rzv  [--same--]  changed antecedent from -. A = (/) to A =/= (/)
 5-Oct-06 r19.45zv  [--same--]  changed antecedent from -. A = (/) to A =/= (/)
 5-Oct-06 r19.27zv  [--same--]  changed antecedent from -. A = (/) to A =/= (/)
 5-Oct-06 r19.36zv  [--same--]  changed antecedent from -. A = (/) to A =/= (/)
 5-Oct-06 iindif2   [--same--]  changed antecedent from -. A = (/) to A =/= (/)
 5-Oct-06 r19.28zv  [--same--]  changed antecedent from -. A = (/) to A =/= (/)
 5-Oct-06 r19.3rzv  [--same--]  changed antecedent from -. A = (/) to A =/= (/)
 2-Oct-06 phplem5   phplem4
 2-Oct-06 phplem4   phplem3
 2-Oct-06 phplem3   phplem2
 2-Oct-06 phplem2   phplem1
 2-Oct-06 phplem1   ---         obsolete; use difsnid
29-Sep-06 uniord    orduni
29-Sep-06 onunit    ssonuni
29-Sep-06 onuni     ssonunii
29-Sep-06 ac6s2     ac6s3
29-Sep-06 ac6c      ---         obsolete; use ac6s5
21-Sep-06 rankuni   rankuni2
20-Sep-06 npnz      [--same--]  strengthened by adding converse
20-Sep-06 onsucuni2 [--same--]  swapped arguments of = sign
19-Sep-06 nlimsuc   ---         obsolete; use nlimsucg
19-Sep-06 limuni2   limuni3
15-Sep-06 ranklon   rankval4
13-Sep-06 cbvop     rexxp
11-Sep-06 zfaus     zfauscl
10-Sep-06 fex       [--same--]  antecedent changed to use conjunction & swapped
10-Sep-06 f1dmex    [--same--]  antecedent changed to use conjunction & swapped
10-Sep-06 fnex      [--same--]  antecedent changed to use conjunction & swapped
10-Sep-06 ssexg     [--same--]  antecedent changed to use conjunction & swapped
10-Sep-06 funimaexg [--same--]  antecedent changed to use conjunction & swapped
10-Sep-06 resfunexg [--same--]  antecedent changed to use conjunction & swapped
 9-Sep-06 funex     [--same--]  antecedent changed to use conjunction & swapped
 8-Sep-06 cls       clsp
29-Aug-06 elab3g    elab3
26-Aug-06 unop      uniop
26-Aug-06 unpr      unipr
26-Aug-06 unictb    [--same--]  removed irrelevant hypothesis
16-Aug-06 ssrab     ssrab2
16-Aug-06 rabss     rabss2
16-Aug-06 ssab      ssab2
13-Aug-06 fvco3     [--same--]  antecedent changed to use triple conjunction
13-Aug-06 fvco2     [--same--]  antecedent changed to use triple conjunction
 6-Jun-06 sq0       sq00
 1-Jun-06 infpn     infpn2
27-May-06 ---       ---         exp was changed to ex to prevent matching
27-May-06 ---       ---           math token 'exp'.
27-May-06 exp       ex
26-May-06 f1ocnvfvb [--same--]  antecedent changed to use triple conjunction
22-Apr-06 fvco      [--same--]  antecedent changed to use triple conjunction
10-Apr-06 plus1let  p1let
10-Apr-06 leplus1t  lep1t
10-Apr-06 ltplus1   ltp1
10-Apr-06 ltplus1t  ltp1t
29-Mar-06 xpdom2    [--same--]  eliminated the A e. _V hypothesis
29-Mar-06 xpdom1    [--same--]  eliminated the A e. _V hypothesis
28-Mar-06 sspr      [--same--]  eliminated both $e hypotheses
26-Mar-06 fnfvop    fnopfvb
26-Mar-06 fnfvbr    fnbrfvb
26-Mar-06 eqri      eqriv
26-Mar-06 eqrd      eqrdv
26-Mar-06 nn0z      nn0zrab
26-Mar-06 nnz       nnzrab
24-Mar-06 fodomb    [--same--]  eliminated the B e. _V hypothesis
24-Mar-06 eldmg     eldm2g
22-Mar-06 prprc     prprc1
22-Mar-06 sqrsqet   sqrsqt
22-Mar-06 sqrsqe    sqrsq
22-Mar-06 sqrsq     sqrmsq2
21-Mar-06 nn0le2sqet nn0le2msqt
21-Mar-06 le2sqet   le2sqt
21-Mar-06 le2sqt    le2msqt
21-Mar-06 lt2sqet   lt2sqt
21-Mar-06 lt2sqt    lt2msqt
21-Mar-06 le2sqe    le2sq
21-Mar-06 le2sq     le2msq
21-Mar-06 lt2sqe    lt2sq
21-Mar-06 lt2sq     lt2msq
21-Mar-06 ltsqt     ltmsqt
13-Mar-06 sq11t     [--same--]  rearranged antecedent
11-Mar-06 sqrecl    resqcl
11-Mar-06 sqreclt   resqclt
11-Mar-06 ---       ---         'sq' is normal square (A ^ 2)
11-Mar-06 sqe0      sqeq0
11-Mar-06 sqe11     sq11
11-Mar-06 sqegt0    sqgt0
11-Mar-06 sqege0    sqge0
11-Mar-06 sqe11t    sq11t
11-Mar-06 sqege0t   sqge0t
11-Mar-06 ---       ---         'msq' is square represented by mult. (A x. A)
11-Mar-06 sqeq0      msq0
11-Mar-06 sqgt0     msqgt0
11-Mar-06 sqge0     msqge0
11-Mar-06 sq11      msq11
11-Mar-06 sqznn     msqznn
11-Mar-06 sqrsqid   sqrmsq
11-Mar-06 sqeq0      msq0
24-Feb-06 lerect    [--same--]  rearranged antecedent
24-Feb-06 ltrect    [--same--]  rearranged antecedent
24-Feb-06 lt2sqet   [--same--]  rearranged antecedent
24-Feb-06 le2sqet   [--same--]  rearranged antecedent
24-Feb-06 lt2sqt    [--same--]  rearranged antecedent
24-Feb-06 le2sqt    [--same--]  rearranged antecedent
20-Feb-06 funfvopi  funopfv
20-Feb-06 funopfv   funfvop
20-Feb-06 funfvop   funopfvb
 9-Feb-06 divneq0bt divne0bt
 9-Feb-06 divneq0   divne0
 9-Feb-06 recneq0z  recne0z
 9-Feb-06 pm2.61an2 pm2.61dan
 9-Feb-06 pm2.61an1 pm2.61ian
28-Jan-06 cleqfvf   eqfnfvf
26-Jan-06 fri       [--same--]  changed to closed theorem instead of inference
17-Jan-06 relin     relin1
17-Jan-06 ssrelqqq  relss
17-Jan-06 relss     ssrel
17-Jan-06 ssrel     ssrelqqq
16-Jan-06 elrnqqq   elrn2
16-Jan-06 elrn2     elrn
16-Jan-06 elrn      elrnqqq
12-Jan-06 df-ef     [--same--]  revised to use new df-sum
 9-Jan-06 rabeqbi2i rabeq2i
 9-Jan-06 abeqbi2   abeq2
 9-Jan-06 abeqbi1   abeq1
 9-Jan-06 abeqbi2i  abeq2i
 9-Jan-06 abeqbi1i  abeq1i
 9-Jan-06 abeqbi2d  abeq2d
 9-Jan-06 abbieq2i  abbi2i
 9-Jan-06 abbieqi   abbii
 9-Jan-06 abbieqd   abbid
 9-Jan-06 abbieqdv  abbidv
 9-Jan-06 abbieq2dv abbi2dv
 9-Jan-06 abbieq1dv abbi1dv
 9-Jan-06 rabbieqi  rabbii
 9-Jan-06 rabbieqdv rabbidv
 9-Jan-06 rabbieqsdv rabbisdv
 9-Jan-06 rabbieqrdv rabbirdv
 9-Jan-06 opabbieqd opabbid
 9-Jan-06 opabbieqdv opabbidv
 9-Jan-06 oprabbieqd oprabbid
 9-Jan-06 oprabbieqdv oprabbidv
 9-Jan-06 oprabbieqi oprabbii
 9-Jan-06 abeqbi2   abeq2
 9-Jan-06 abeqbi2i  abeq2i
 9-Jan-06 abeqbi1   abeq1
 9-Jan-06 abeqbi2d  abeq2d
 9-Jan-06 abeqbi1i  abeq1i
 9-Jan-06 rabeqbi2i rabeq2i
 9-Jan-06 oprabbieqi oprabbii
 7-Jan-06 divgt0lem divgt0i2
 5-Jan-06 lep1t  letrp1t
 4-Jan-06 nnegdift  ---         obsolete; use subge0t (swapped biconditional)
 2-Jan-06 opabbii.2 opabbii
 1-Jan-06 negdi2    negsubdi
 1-Jan-06 negdi2t   negsubdit
 1-Jan-06 negdi3    negsubdi2t
 1-Jan-06 negdi3t   negsubdi2t
17-Dec-05 msca      ---         obsolete; now embedded inside equs4 proof
16-Dec-05 1expt     [--same--]  antecedent extended from NN to NN0
16-Dec-05 nnexpclt  [--same--]  antecedent extended from NN to NN0
16-Dec-05 nn0expclt [--same--]  antecedent extended from NN to NN0
16-Dec-05 zexpclt   [--same--]  antecedent extended from NN to NN0
16-Dec-05 qexpclt   [--same--]  antecedent extended from NN to NN0
16-Dec-05 reexpclt  [--same--]  antecedent extended from NN to NN0
16-Dec-05 expclt    [--same--]  antecedent extended from NN to NN0
16-Dec-05 expcllem  [--same--]  antecedent extended from NN to NN0; + 3rd hyp.
16-Dec-05 expp1t    [--same--]  antecedent extended from NN to NN0
16-Dec-05 expvalt   expnnvalt
13-Dec-05 sbcco     sbccog
 1-Dec-05 subneg2t  subnegt
 1-Dec-05 subnegt   ---         obsolete; use negsubt (swapped equality)
 1-Dec-05 subneg    ---         obsolete; use negsub (swapped equality)
 1-Dec-05 reueq     reueq1
 1-Dec-05 rexeq     rexeq1
 1-Dec-05 raleq     raleq1
 1-Dec-05 reueqf    reueq1f
 1-Dec-05 rexeqf    rexeq1f
 1-Dec-05 raleqf    raleq1f
 1-Dec-05 ad2antxx  ad2antrr
 1-Dec-05 ad2antrr  ad2antll
 1-Dec-05 ad2antll  ad2antxx
29-Nov-05 sbcel2    sbcel2gv
29-Nov-05 sbcel1    sbcel1gv
28-Nov-05 sbcn      sbcng
28-Nov-05 sbcim     sbcimg
28-Nov-05 sbcbi     sbcbig
28-Nov-05 sbcor     sbcorg
28-Nov-05 sbcan     sbcang
28-Nov-05 sbcal     sbcalg
28-Nov-05 sbcex     sbcexg
28-Nov-05 sbceq1    sbceq1a
21-Nov-05 2o        2on
21-Nov-05 1o        1on
19-Nov-05 zfrep3    axrep5
19-Nov-05 zfrep2    axrep4
19-Nov-05 axrep     axrep2
18-Nov-05 hbsbcg    hbsbc1g
18-Nov-05 hbsbc     hbsbc1
18-Nov-05 hbsbcv    hbsbc1v
18-Nov-05 ---       ---         More changes to the bixx series below -
18-Nov-05 ---       ---         changed to xxbix to be analogous to the xxeqx
18-Nov-05 ---       ---         series e.g. uneq12d.  Also, the bi(r)abxx were
18-Nov-05 ---       ---         changed to (r)abbieqxx: "bi" in hyp. and
18-Nov-05 ---       ---         "eq" in conclusion.
18-Nov-05 bial      albii
18-Nov-05 bi2al     2albii
18-Nov-05 biex      exbii
18-Nov-05 bi2ex     2exbii
18-Nov-05 bi3ex     3exbi
18-Nov-05 biald     albid
18-Nov-05 biexd     exbid
18-Nov-05 bisb      sbbii
18-Nov-05 bisbd     sbbid
18-Nov-05 bialdv    albidv
18-Nov-05 biexdv    exbidv
18-Nov-05 bi2aldv   2albidv
18-Nov-05 bi2exdv   2exbidv
18-Nov-05 bi3exdv   3exbidv
18-Nov-05 bi4exdv   4exbidv
18-Nov-05 bieud     eubid
18-Nov-05 bieudv    eubidv
18-Nov-05 bieu      eubii
18-Nov-05 bimod     mobid
18-Nov-05 bimo      mobii
18-Nov-05 biralda   ralbida
18-Nov-05 birexda   rexbida
18-Nov-05 biraldva  ralbidva
18-Nov-05 birexdva  rexbidva
18-Nov-05 birald    ralbid
18-Nov-05 birexd    rexbid
18-Nov-05 biraldv   ralbidv
18-Nov-05 birexdv   rexbidv
18-Nov-05 biraldv2  ralbidv2
18-Nov-05 birexdv2  rexbidv2
18-Nov-05 biral     ralbii
18-Nov-05 birex     rexbii
18-Nov-05 bi2ral    2ralbii
18-Nov-05 bi2rex    2rexbii
18-Nov-05 biral2    ralbii2
18-Nov-05 birex2    rexbii2
18-Nov-05 birala    ralbiia
18-Nov-05 birexa    rexbiia
18-Nov-05 bi2rexa   2rexbiia
18-Nov-05 bi2ralda  2ralbida
18-Nov-05 bi2raldva 2ralbidva
18-Nov-05 bi2rexdva 2rexbidva
18-Nov-05 bireudva  reubidva
18-Nov-05 bireudv   reubidv
18-Nov-05 bireua    reubiia
18-Nov-05 bireu     reubii
18-Nov-05 bisbcdv   sbcbidv
18-Nov-05 bisbc     sbcbii
18-Nov-05 eqrabi    rabeqbi2i
18-Nov-05 eqab      abeqbi2
18-Nov-05 eqabr     abeqbi1
18-Nov-05 eqabi     abeqbi2i
18-Nov-05 eqabri    abeqbi1i
18-Nov-05 eqabd     abeqbi2d
18-Nov-05 biabri    abbieq2i
18-Nov-05 biabi     abbieqi
18-Nov-05 biabd     abbieqd
18-Nov-05 biabdv    abbieqdv
18-Nov-05 biabrdv   abbieq2dv
18-Nov-05 biabldv   abbieq1dv
18-Nov-05 birabi    rabbieqi
18-Nov-05 birabdv   rabbieqdv
18-Nov-05 birabsdv  rabbieqsdv
18-Nov-05 birabrdv  rabbieqrdv
18-Nov-05 biopabd   opabbieqd
18-Nov-05 biopabdv  opabbieqdv
18-Nov-05 bioprabd  oprabbieqd
18-Nov-05 bioprabdv oprabbieqdv
18-Nov-05 bioprabi  oprabbieqi
18-Nov-05 bicon1i   con1bii
18-Nov-05 bicon2i   con2bii
18-Nov-05 bicon4i   con4bii
18-Nov-05 bicon4d   con4bid
18-Nov-05 bicon2    con2bi
18-Nov-05 bicon2d   con2bid
18-Nov-05 bicon1d   con1bid
18-Nov-05 bisyl7    syl7ib
18-Nov-05 bisyl8    syl8ib
11-Nov-05 sbcbidv   [--same--]  swapped antecedents
21-Oct-05 ciin      [--same--]  "|^|" changed to "|^|_"
21-Oct-05 cuin      [--same--]  "U." changed to "U_"
21-Oct-05 ---SYMBOL CHANGE----  Changed "|^|" to "|^|_" in thm's using ciin
21-Oct-05 ---SYMBOL CHANGE----  Changed "U." to "U_" in thm's using ciun
20-Oct-05 rax5      ra5
20-Oct-05 rax4      ---         obsolete; use ra4sbc
20-Oct-05 reuuni2f  [--same--]  weakened its hypotheses
19-Oct-05 reuss     [--same--]  antecedent changed to use triple conjunction
10-Oct-05 uzwo      [--same--]  changed to use ZZ>= notation
10-Oct-05 uzwo2     [--same--]  changed to use ZZ>= notation
 1-Oct-05 nnncant   nnncan1t
13-Sep-05 leltnet   [--same--]  antecedent changed to use triple conjunction
10-Sep-05 ifel      ifcl
 6-Sep-05 dmopab2   dmopab3
 5-Sep-05 peano2uz  peano2uz2
 1-Sep-05 cleqfv    eqfnfv
 1-Sep-05 df-seq    df-seq1
 1-Sep-05 cseqz     cseq1
 1-Sep-05 serft     ser1ft
 1-Sep-05 serf      ser1f
 1-Sep-05 sercl     ser1cl
 1-Sep-05 serrecl   ser1recl
 1-Sep-05 serre     ser1re
 1-Sep-05 sercl2    ser1cl2
 1-Sep-05 serf2     ser1f2
 1-Sep-05 ser12     ser11
 1-Sep-05 sersuc2   ser1p1
 1-Sep-05 sermono   ser1mono
 1-Sep-05 seradd2   ser1add2
 1-Sep-05 seradd    ser1add
 1-Sep-05 serdir    ser1dir
 1-Sep-05 serabsdiflem ser1absdiflem
 1-Sep-05 serabsdif ser1absdif
 1-Sep-05 serre2    ser1re2
 1-Sep-05 sercj     ser1cj
 1-Sep-05 serconst  ser1const
 1-Sep-05 sertrunclem ser1trunclem
 1-Sep-05 sercmp    ser1cmp
 1-Sep-05 sercmp0   ser1cmp0
 1-Sep-05 sercmp2lem ser1cmp2lem
 1-Sep-05 sercmp2   ser1cmp2
 1-Sep-05 seqlem1   seq1lem1
 1-Sep-05 seqlem2   seq1lem2
 1-Sep-05 seqrval   seq1rval
 1-Sep-05 seqval    seq1val
 1-Sep-05 seqfnlem  seq1fnlem
 1-Sep-05 seqval2   seq1val2
 1-Sep-05 seq1lem   seq11lem
 1-Sep-05 seqsuclem seq1suclem
 1-Sep-05 seqp1     seq1p1
 1-Sep-05 seqm1     seq1m1
 1-Sep-05 seqfn     seq1fn
 1-Sep-05 seqrn     seq1rn2
 1-Sep-05 seqrn2    seq1rn
 1-Sep-05 seqcl     seq1cl
 1-Sep-05 seqres    seq1res
 1-Sep-05 seqbnd    seq1bnd
 1-Sep-05 sequblem  seq1ublem
 1-Sep-05 sequb     seq1ub
 1-Sep-05 seqhcau   seq1hcau
 1-Sep-05 ---SYMBOL CHANGE----  Changed math symbol 'seq' to 'seq1'
 1-Sep-05 seq1      seq11       Warning: do _before_ the symbol change above
17-Aug-05 df-clim   [--same--]  The old df-clim, df-shft, and df-seq0, and
17-Aug-05 df-shft   [--same--]      all derived theorems, have been scrapped
17-Aug-05 df-seq0   [--same--]      or rederived from the new definitions.
30-Jul-05 ---       ---         syl* changes below were sugg'ed by Scott Fenton
30-Jul-05 syl34d    imim12d
30-Jul-05 syl4d     imim1d
30-Jul-05 syl3d     imim2d
30-Jul-05 syl34     imim112i
30-Jul-05 syl4      imim1i
30-Jul-05 syl3      imim2i
30-Jul-05 syl2      imim1
30-Jul-05 syl1      imim2
27-Jul-05 uzind     [--same--]  weaker basis hyp.; different mand. hyp. order
13-Jul-05 mp3an11   mp3anl1
13-Jul-05 mp3an12   mp3anl2
13-Jul-05 mp3an13   mp3anl3
13-Jul-05 syl3an11  syl3anl1
13-Jul-05 syl3an12  syl3anl2
13-Jul-05 syl3an13  syl3anl3
13-Jul-05 mpan11    mpanl1
13-Jul-05 mpan12    mpanl2
13-Jul-05 mpan21    mpanr1
13-Jul-05 mpan22    mpanr2
13-Jul-05 sylan11   sylanl1
13-Jul-05 sylan12   sylanl2
13-Jul-05 sylan21   sylanr1
13-Jul-05 sylan22   sylanr2
13-Jul-05 mpan121   mpanlr1
13-Jul-05 ecased    ---         obsolete; use ecase23d (diff. hyp. order)
11-Jul-05 lelt      lenlt
11-Jul-05 leltt     lenltt
11-Jul-05 lenltt    eqleltt
10-Jul-05 bcpasc    bcpasc2
10-Jul-05 bcvalt    bcval2t
 9-Jul-05 sermconst ---         obsolete; use ser1mulc
 9-Jul-05 seqsuc    seq1p1
 3-Jul-05 peano5c   ---         obsolete; use peano5nn (restr. qntfr.)
 3-Jul-05 df-n      [--same--]  shortened with restricted quantifier
 2-Jul-05 mulge0t   [--same--]  conjoined antecedents
 2-Jul-05 prodgt02t [--same--]  swapped A e. RR and B e. RR
27-Jun-05 syl3an    [--same--]  changed order of hypotheses
25-Jun-05 ecoprcom  [--same--]  changed order of $f hypotheses
21-Jun-05 nn0ltlem1 nn0ltlem1t
21-Jun-05 subsub    subsub23
17-Jun-05 ecoprdist ---         obsolete; use ecoprdi
16-Jun-05 binom     binom2
12-Jun-05 oel       orabs
30-May-05 ltdiv23t  [--same--]  conjoined antecedents
30-May-05 ledivt    lediv1t
23-May-05 rcla42v   [--same--]  swapped antecedents
23-May-05 rcla4v    [--same--]  swapped antecedents
23-May-05 rcla4     [--same--]  swapped antecedents
10-May-05 mpbiranr  mpbiran2
 8-May-05 funfv2    [--same--]  changed to A F y instead of <. A , y >. e. F
 8-May-05 imasn     ---         obsolete; use relimasn (A R y instead of o.p.)
 3-May-05 nndiv     nndivt
 2-May-05 subaddeq  pncan3
 2-May-05 subaddeqt pncan3t
 1-May-05 divne0bt  [--same--]  changed antecedent to triple conjunction
 1-May-05 divcan2t  [--same--]  changed antecedent to triple conjunction
 1-May-05 divcan1t  [--same--]  changed antecedent to triple conjunction
30-Apr-05 divnegt   [--same--]  changed antecedent to triple conjunction
30-Apr-05 divrect   [--same--]  changed antecedent to triple conjunction
30-Apr-05 divcan3t  [--same--]  changed antecedent to triple conjunction
30-Apr-05 divcan4t  [--same--]  changed antecedent to triple conjunction
29-Apr-05 crut      [--same--]  generalized -> to <->
29-Apr-05 cru       [--same--]  generalized -> to <->
29-Apr-05 isqm1     itimesi
29-Apr-05 crmult    crmul       changed hypotheses from real to complex
29-Apr-05 redivclt  [--same--]  changed antecedent to triple conjunction
29-Apr-05 divclt    [--same--]  changed antecedent to triple conjunction
28-Apr-05 ine0      [--same--]  changed -. and = to =/=
27-Apr-05 ltdivt    ltdiv1t
27-Apr-05 ltdiv     ltdiv1
27-Apr-05 ltdivi    ltdiv1i
24-Apr-05 prodgt0   [--same--]  strengthened 0 < A to 0 <_ A
24-Apr-05 prodgt0i  prodgt0lem
 7-Apr-05 equs2     ---         obsolete; use equs5
 7-Apr-05 equs1     ---         obsolete; use equs4
 6-Apr-05 absltt    [--same--]  swapped & contraposed conjunct with -u
 6-Apr-05 absle     [--same--]  swapped & contraposed conjunct with -u
 6-Apr-05 abslt     [--same--]  swapped & contraposed conjunct with -u
26-Mar-05 abscj     [--same--]  swapped arguments of = sign
18-Mar-05 reim0     reim0b
18-Mar-05 rere      rereb
18-Mar-05 cjre      cjreb
18-Mar-05 negre     negreb
11-Mar-05 frsuc     frsuc
10-Mar-05 nn0addge2 [--same--]  Generalized 1st hyp from NN0 to RR
10-Mar-05 nn0addge1 [--same--]  Generalized 1st hyp from NN0 to RR
 5-Mar-05 chv       chvarv
 5-Mar-05 chv2      chvar
 4-Mar-05 divdistr  divdir
 4-Mar-05 divdistrz divdirz
 4-Mar-05 divge0t   [--same--]  conjoined the two left-most antecedents
 4-Mar-05 divgt0t   [--same--]  conjoined the two left-most antecedents
 4-Mar-05 absgt0t   [--same--]  changed  -. A = 0  to  A =/= 0
 4-Mar-05 absgt0    [--same--]  changed  -. A = 0  to  A =/= 0
24-Feb-05 absidt    [--same--]  conjoined the two left-most antecedents
27-Feb-05 del34     ---         obsolete; use dral1 instead
27-Feb-05 del35     ---         obsolete; use dral1 instead
27-Feb-05 del34b    dral1
27-Feb-05 del36     ---         obsolete; use dral2 instead
27-Feb-05 del40     ---         obsolete; use drex1 instead
27-Feb-05 del41     ---         obsolete; use drex1 instead
27-Feb-05 del42     ---         obsolete; use drex2 instead
27-Feb-05 del43     ---         obsolete; use drsb1 instead
27-Feb-05 del43b    drsb1
27-Feb-05 del44     ---         obsolete; use drsb2 instead
27-Feb-05 del45     ---         obsolete; use drsb2 instead
27-Feb-05 ddelimf2  dvelimf2
27-Feb-05 ddelimf   dvelimf
27-Feb-05 ddelimdf  dvelimdf
27-Feb-05 ddelim    dvelim
27-Feb-05 ddeeq1    dveeq1
27-Feb-05 ddeeq2    dveeq2
27-Feb-05 ddeel1    dveel1
27-Feb-05 ddeel2    dveel2
24-Feb-05 bi3ord    3orbi123d
24-Feb-05 im3ord    3orim123d
24-Feb-05 bi3or     3orbi123i
24-Feb-05 bi3an     3anbi123i
24-Feb-05 bi3and    3anbi123d
24-Feb-05 im3an     3anim123i
24-Feb-05 divdistrt divdirt
24-Feb-05 ltdiv1t   [--same--]  conjoined the two left-most antecedents
24-Feb-05 lediv1t   [--same--]  conjoined the two left-most antecedents
24-Feb-05 ltmuldivt [--same--]  conjoined the two left-most antecedents
24-Feb-05 ltdivmult [--same--]  conjoined the two left-most antecedents
24-Feb-05 ltmuldiv2t [--same--]  conjoined the two left-most antecedents
24-Feb-05 gt0ne0t   [--same--]  conjoined the two left-most antecedents
24-Feb-05 ltrect    [--same--]  conjoined the two left-most antecedents
24-Feb-05 recgt0t   [--same--]  conjoined the two left-most antecedents
24-Feb-05 lerect    [--same--]  conjoined the two left-most antecedents
21-Feb-05 nn0ge0i   nn0ge0
21-Feb-05 rdgzer    rdg0
21-Feb-05 rdgzert   rdg0g
21-Feb-05 frzer     fr0g
21-Feb-05 mulzer1   mul01
21-Feb-05 mulzer2   mul02
21-Feb-05 mulzer1t  mul01t
21-Feb-05 mulzer2t  mul02t
21-Feb-05 divzer    div0
19-Feb-05 ax0re     0re
13-Feb-05 cardcard  cardidm
13-Feb-05 exp2t     sqvalt
13-Feb-05 uzind2    ---         Obsolete; use uzind3
 5-Feb-05 ---       ---         We will adopt "equ" (vs. old "eq") for
 5-Feb-05 ---       ---         set variable equality and "eq" (vs. old
 5-Feb-05 ---       ---         "cleq") for class equality.  (Remember it
 5-Feb-05 ---       ---         is important to do these in REVERSE order
 5-Feb-05 ---       ---         below!)
 5-Feb-05 cleqri    eqri
 5-Feb-05 cleqrd    eqrd
 5-Feb-05 cleqid    eqid
 5-Feb-05 cleqcom   eqcom
 5-Feb-05 cleqcomi  eqcomi
 5-Feb-05 cleqcomd  eqcomd
 5-Feb-05 cleq1     eqeq1
 5-Feb-05 cleq2     eqeq2
 5-Feb-05 cleq1i    eqeq1i
 5-Feb-05 cleq2i    eqeq2i
 5-Feb-05 cleq1d    eqeq1d
 5-Feb-05 cleq2d    eqeq2d
 5-Feb-05 cleq12    eqeq12
 5-Feb-05 cleq12i   eqeq12i
 5-Feb-05 cleq12d   eqeq12d
 5-Feb-05 cleqan12d eqeqan12d
 5-Feb-05 cleqan12rd eqeqan12rd
 5-Feb-05 cleqtr    eqtr
 5-Feb-05 cleq2tr   eq2tri
 5-Feb-05 cleqab    abeqbi2
 5-Feb-05 cleqabi   abeqbi2i
 5-Feb-05 cleqabr   abeqbi1
 5-Feb-05 cleqabd   abeqbi2d
 5-Feb-05 cleqabri  abeqbi1i
 5-Feb-05 cleq2ab   eq2ab
 5-Feb-05 cleqrabi  rabeqbi2i
 5-Feb-05 clneq     nelneq
 5-Feb-05 clneq2    nelneq2
 5-Feb-05 sbeq2     equsb2
 5-Feb-05 sbeq1     equsb1
 5-Feb-05 eqvin.l2  ---           obsolete; use equvin instead
 5-Feb-05 eqvin     equvin
 5-Feb-05 eqvin.l1  equvini
 5-Feb-05 eqsal     equsal
 5-Feb-05 eqsex     equsex
 5-Feb-05 eqs5      equs5
 5-Feb-05 eqs4      equs4
 5-Feb-05 eqs3      equs3
 5-Feb-05 eqs2      equs2
 5-Feb-05 eqs1      equs1
 5-Feb-05 eq6s      hbnaes
 5-Feb-05 eq6       hbnae
 5-Feb-05 eq5s      hbaes
 5-Feb-05 eq5       hbae
 5-Feb-05 eq4ds     nalequcoms
 5-Feb-05 eq4s      alequcoms
 5-Feb-05 eq4       ax-10
 5-Feb-05 a14b      elequ2
 5-Feb-05 a13b      elequ1
 5-Feb-05 eqt2b     equequ2
 5-Feb-05 a8b       equequ1
 5-Feb-05 eqt       equtr
 5-Feb-05 eqt2      equtrr
 5-Feb-05 eqan      equtr2
 5-Feb-05 eqcom     equcomi
 5-Feb-05 eqcomb    equcom
 5-Feb-05 eqcoms    equcoms
 5-Feb-05 eqid      equid
 3-Feb-05 sb5f1     sb6rf
21-Jan-05 mulcanxx  mulcant2
21-Jan-05 mulcant2  mulcant
21-Jan-05 mulcant   mulcanxx
10-Jan-05 add41r3   add42
10-Jan-05 caopr41r3 caopr42
10-Jan-05 an41r3s   an42s
10-Jan-05 an41r3    an42
 8-Jan-05 ---       ---         The imxx series was changed analogously
 8-Jan-05 ---       ---         to the bixx series change.
 8-Jan-05 im2an     anim12i
 8-Jan-05 imran     anim1i
 8-Jan-05 imlan     anim2i
 8-Jan-05 im2or     orim12i
 8-Jan-05 imror     orim1i
 8-Jan-05 imlor     orim2i
 8-Jan-05 im2and    anim12d
 8-Jan-05 imrand    anim1d
 8-Jan-05 imland    anim2d
 8-Jan-05 im2ord    orim12d
 8-Jan-05 imrord    orim1d
 8-Jan-05 imlord    orim2d
 8-Jan-05 ---       ---         The bixx series was changed to be analogous
 8-Jan-05 ---       ---         to the xxeqx series e.g. uneq12d.
 8-Jan-05 ---       ---         (Suggested by Raph Levien.)
 8-Jan-05 bi2and    anbi12d
 8-Jan-05 birand    anbi1d
 8-Jan-05 biland    anbi2d
 8-Jan-05 bi2imd    imbi12d
 8-Jan-05 birimd    imbi1d
 8-Jan-05 bilimd    imbi2d
 8-Jan-05 bi2ord    orbi12d
 8-Jan-05 birord    orbi1d
 8-Jan-05 bilord    orbi2d
 8-Jan-05 bi2bid    bibi12d
 8-Jan-05 birbid    bibi1d
 8-Jan-05 bilbid    bibi2d
 8-Jan-05 binegd    negbid
 8-Jan-05 bi2an     anbi12i
 8-Jan-05 biran     anbi1i
 8-Jan-05 bilan     anbi2i
 8-Jan-05 bi2im     imbi12i
 8-Jan-05 birim     imbi1i
 8-Jan-05 bilim     imbi2i
 8-Jan-05 bi2or     orbi12i
 8-Jan-05 biror     orbi1i
 8-Jan-05 bilor     orbi2i
 8-Jan-05 bi2bi     bibi12i
 8-Jan-05 birbi     bibi1i
 8-Jan-05 bilbi     bibi2i
 8-Jan-05 bineg     negbii
 3-Jan-05 pm5.41    imdi
 1-Jan-05 iundif    iundif2
 1-Jan-05 iindif    iindif2
 1-Jan-05 iunin     iunin2
 1-Jan-05 iinin     iinin2
 1-Jan-05 sylan13br sylancbr
 1-Jan-05 sylan13b  sylancb
 1-Jan-05 sylan13   sylanc
 1-Jan-05 syl13     sylc
26-Dec-04 0ne1o     ---         obsolete; use 1ne0
19-Dec-04 sbequ6    [--same--]  swapped biconditional order
19-Dec-04 sbequ5    [--same--]  swapped biconditional order
15-Dec-04 syl2and   syl2ani
15-Dec-04 sylan2d   sylan2i
15-Dec-04 syland    sylani
12-Dec-04 nnordex   nnaordex
12-Dec-04 nnwordex  nnawordex
12-Dec-04 mpand     mpdan
12-Dec-04 ontr      ontr1
 6-Dec-04 on0eqel   on0eqelt
30-Nov-04 exp2      sqvalt
30-Nov-04 1exp      1expt
30-Nov-04 0exp      0expt
30-Nov-04 exp1      exp1t
30-Nov-04 expp1     expp1t
18-Nov-04 divrclz   redivclz
18-Nov-04 divrclt   redivclt
18-Nov-04 subrclt   resubclt
18-Nov-04 negrclt   renegclt
18-Nov-04 mulrclt   remulclt
18-Nov-04 divrcl    redivcl
18-Nov-04 subrcl    resubcl
18-Nov-04 negrcl    renegcl
18-Nov-04 mulrcl    remulcl
18-Nov-04 addrcl    readdcl
18-Nov-04 ltdivmul  ---         obsolete; use ltmuldiv instead
18-Nov-04 ltdivmult ---         obsolete; use ltmuldivt instead (note: there
                                is a new ltdivmult that is unrelated)
18-Nov-04 distr2t   adddirt
18-Nov-04 distr2    adddir
18-Nov-04 distr     adddi
18-Nov-04 subdistr  subdir
17-Nov-04 nnrect    nnrecgt0t
17-Nov-04 posdif    [--same--]  swapped biconditional and variable order
15-Nov-04 negdistt3 negdi3t
15-Nov-04 negdistt2 negdi2t
15-Nov-04 negdistt  negdit
15-Nov-04 negdist3  negdi3
15-Nov-04 negdist2  negdi2
11-Nov-04 reuunis   reuuni2
11-Nov-04 reuuni    reuuni1
 9-Nov-04 zlelt1    zleltp1t
 9-Nov-04 zltle1    zltp1let
 7-Sep-04 arch      [--same--]  removed quantifier, changed set var. to class
 2-Nov-04 dfom2     dfom3
 2-Nov-04 dfom3     dfom4
29-Oct-04 df-ded    df-if
29-Oct-04 dedeq1    ifeq1
29-Oct-04 dedeq2    ifeq2
29-Oct-04 dedeq12   ifeq12
29-Oct-04 dedbi     ifbi
29-Oct-04 dedlem1   iftrue
29-Oct-04 dedlem2   iffalse
29-Oct-04 dedex     ifex
29-Oct-04 cded      cif
29-Oct-04 ---SYMBOL CHANGE----  Changed math symbol 'ded' to 'if'
28-Oct-04 cmulc     cmul
20-Oct-04 oprabex   oprabex2
14-Oct-04 nn0lelt1  nn0leltp1t
14-Oct-04 nn0ltle1  nn0ltp1let
14-Oct-04 nnlelt1   nnleltp1t
14-Oct-04 nnltle1   nnltp1let
14-Oct-04 rnoel3    rabn0
14-Oct-04 noel3     abn0
14-Oct-04 noel2     n0i
14-Oct-04 peano2c   peano2nn
12-Oct-04 supeu     supeui
12-Oct-04 supcl     supcli
12-Oct-04 supub     supubi
12-Oct-04 suplub    suplubi
12-Oct-04 supnub    supnubi
12-Oct-04 suprcl    suprcli
12-Oct-04 suprub    suprubi
12-Oct-04 pm4.12    con2bi
12-Oct-04 bicon4    con4bii
12-Oct-04 con2bi    con2bii
12-Oct-04 bicon1    con1bii
12-Oct-04 pm2.11    exmid
11-Oct-04 sbf1      ---         obsolete; use sbf instead
11-Oct-04 ceqsexg   ceqex
 9-Oct-04 fvco2     fvco3
 8-Oct-04 indif0    disjdif
 8-Oct-04 biopab    opabbii.2
 8-Oct-04 bioprab   oprabbieqi
 7-Oct-04 ssii      sselii
 6-Oct-04 op2nd     op2ndb
 6-Oct-04 op1st     op1stb
 3-Oct-04 ind       nnind
 3-Oct-04 sylan5    sylan2
 3-Oct-04 sylan5b   sylan2b
 3-Oct-04 sylan5br  sylan2br
 3-Oct-04 sylan5d   sylan2i
 3-Oct-04 zind      ---         obsolete; use uzind
30-Sep-04 fvop      funfvop
30-Sep-04 funfvop   funopfv
30-Sep-04 pm4.21    bicom
30-Sep-04 bicom     bicomi
30-Sep-04 entr      entri
30-Sep-04 sstr2qqq  sstr
30-Sep-04 sstr      sstr2
30-Sep-04 sstr2     sstr2qqq
29-Sep-04 xp0qqq    xp0r
29-Sep-04 xp0r      xp0
29-Sep-04 xp0       xp0qqq
28-Sep-04 xpdom     xpdom2      changed variable names
28-Sep-04 xpdom2    xpdom3
26-Sep-04 xpindi    inxp
26-Sep-04 xpun1     xpundi
26-Sep-04 xpun2     xpundir
25-Sep-04 entr      entrt
23-Sep-04 ssfnres   ---         obsolete; use fnssres instead
23-Sep-04 resun     resundi
21-Sep-04 f11       [--same--]  changed o.p. membership to binary relation
21-Sep-04 unisuc    [--same--]  swapped arguments of = sign
21-Sep-04 onunisuc  [--same--]  swapped arguments of = sign
21-Sep-04 undif3    ---         obsolete; use undif
21-Sep-04 ssequn2   [--same--]  swapped arguments of = sign
21-Sep-04 sseqin2   [--same--]  swapped arguments of = sign
21-Sep-04 onelun    [--same--]  swapped arguments of = sign
21-Sep-04 dfss4     [--same--]  swapped arguments of = sign
21-Sep-04 ordunisuc ordunisssuc
21-Sep-04 ssfun     funss
15-Sep-04 19.6      alex
15-Sep-04 alex      alexeq
15-Sep-04 19.11     excom
15-Sep-04 19.11a    excomim
15-Sep-04 19.5      alcom
15-Sep-04 19.7      alnex
15-Sep-04 19.14     exnal
15-Sep-04 alnex     alinexa
15-Sep-04 exnal     exanali
15-Sep-04 dmsn      dmsnop
15-Sep-04 rnsn      rnsnop
13-Sep-04 ppnull    pwpw0
13-Sep-04 pwnull    pw0
13-Sep-04 zfnull2   zfnul
13-Sep-04 nullpss   0pss
13-Sep-04 nullss    0ss
13-Sep-04 nulleq    eq0
13-Sep-04 nnull     n0
13-Sep-04 nnullf    n0f
13-Sep-04 xpdisj    xpsndisj
13-Sep-04 subdist   subdi
13-Sep-04 negdist   negdi
13-Sep-04 nndist    nndi
13-Sep-04 xpindist  inxp
11-Sep-04 ssd       sseld
11-Sep-04 ssi       sseli
11-Sep-04 vtoclab   elab2
11-Sep-04 vtoclabg  elab2g
11-Sep-04 elab2g    elab3g
 6-Sep-04 comm      com12
 4-Sep-04 opabval   fvopab3
 4-Sep-04 opabvalig fvopab3ig
 4-Sep-04 opabval2g fvopab4g
 4-Sep-04 opabval2  fvopab4
 3-Sep-04 undif2    difun2
 1-Sep-04 dedlem2   [--same--]  swapped arguments of = sign
 1-Sep-04 dedlem1   [--same--]  swapped arguments of = sign
31-Aug-04 pm2.16d   con3d
31-Aug-04 pm2.03d   con2d
31-Aug-04 pm2.15d   con1d
31-Aug-04 pm2.16    con3
31-Aug-04 pm2.03    con2
31-Aug-04 pm2.15    con1
31-Aug-04 con3      con3i
31-Aug-04 con2      con2i
31-Aug-04 con1      con1i
29-Aug-04 oprabelrn elrnoprab
27-Aug-04 ssequn1   [--same--]  swapped arguments of = sign
27-Aug-04 df-ss     dfss
27-Aug-04 imdistanb ---         obsolete; use imdistan
27-Aug-04 imdistan  [--same--]  now includes converse
17-Aug-04 difun2    [--same--]  swapped arguments of = sign
17-Aug-04 undif1    [--same--]  swapped arguments of = sign and union
17-Aug-04 difin     [--same--]  swapped arguments of = sign
17-Aug-04 unindistr undir
17-Aug-04 unindist  undi
17-Aug-04 inundistr indir
17-Aug-04 inundist  indi
17-Aug-04 indist    inindi
16-Aug-04 ss2un     unss12      order of variables changed
15-Aug-04 funmo,dffunmof,dffunmo
                    [--same--]  ordered pair membership -> binary relation
15-Aug-04 dfrel2    [--same--]  swapped arguments of = sign
12-Aug-04 unxp      xpundir
11-Aug-04 elima2    elima3
11-Aug-04 reluni    [--same--]  restricted quantifier and added converse
 9-Aug-04 imun      imaun
 3-Aug-04 1id       om1
 3-Aug-04 oalim     [--same--]  conjoined antecedents; now uses indexed union
 3-Aug-04 divdiv23  divdiv23z
 3-Aug-04 divdiv23i divdiv23
 2-Aug-04 divrec,divrecz [--same--] swapped A and B
 2-Aug-04 zq        zqt
 2-Aug-04 qre       qret
 1-Aug-04 mulcant  [--same--]  swapped conjunct in antecedent
 1-Aug-04 axrecex,axrrecex,divclt,divcan1t,divcan2t,recidt,divdistrt,divrclt
                    [--same--]  conjoined the two left-most antecedents
 1-Aug-04 peano1c   1nn
 1-Aug-04 1nn       1onn
28-Jul-04 sbco0     sbid2
28-Jul-04 sbid2     sbid2v
26-Jul-04 cardonval oncardval
15-Jun-04 ssin      [--same--]  swapped biconditional order
15-Jun-04 unss      [--same--]  swapped biconditional order
11-Jun-04 dfun2     df-un
11-Jun-04 df-un     dfun2
11-Jun-04 dfin2     df-in
11-Jun-04 df-in     dfin2
 3-Jun-04 ssintss   intss
 3-Jun-04 intss     intss1
30-May-04 r1clos    r1pwcl      now uses antecedent instead of hypothesis
30-May-04 r1powt    r1pw
28-May-04 sqvalt    ---         obsolete; use exp2
28-May-04 expntwo   exp2
28-May-04 expnone   ---         obsolete; use expp1t
28-May-04 expnsuc   ---         obsolete; use expp1t
28-May-04 expnzer   ---         obsolete; use exp0t
26-May-04 ontrt     ---         obsolete; use onelon instead
26-May-04 ddelim*   [--same--]  (*=wildcard) changed order of hypotheses
21-May-04 fvcnvb    f1ocnvfvb
21-May-04 fvcnv     f1ocnvfv
21-May-04 sbcb      sbcbig    now uses antecedent instead of hypothesis
21-May-04 sbci      sbcimg
21-May-04 sbb       sbbi
21-May-04 sbo       sbor
21-May-04 sbi       sbim
21-May-04 sbim      sbimi
21-May-04 sba       sban
21-May-04 fvelrn    [--same--]  changed to restricted quantifier
 8-Feb-04 zfpowb    pwexb
 8-Feb-04 zfpowcl   pwex
 8-Feb-04 zfnull    0ex
 8-Feb-04 limelon   [--same--]  changed first -> to /\ in antecedent


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                           2. Quick "How To"
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

How to use this file under Windows 95/98/NT/2K/XP/Vista:

1. Download the program metamath.exe per the instructions on the
   Metamath home page (http://us.metamath.org) and put it in the same
   directory as this file (set.mm).
2. In Windows Explorer, double-click on metamath.exe.
3. Type "read set.mm" and press Enter.
4. Type "help" for a list of help topics, and "help demo" for some
   command examples.


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                             3. Bibliography
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Bibliographical references are made by bracketing an identifer in a theorem's
comment, such as [RussellWhitehead].  These refer to HTML tags on the following
web pages:

  Logic and set theory - see http://us.metamath.org/mpegif/mmset.html#bib
  Hilbert space - see http://us.metamath.org/mpegif/mmhil.html#ref


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                      4. Metamath syntax summary
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

The HELP LANGUAGE command in the Metamath program will give you a quick
overview of Metamath.  Syntax summary:

          $c ... $. - Constant declaration
          $v ... $. - Variable declaration
          $d ... $. - Disjoint (distinct) variable restriction
  <label> $f ... $. - "Floating" hypothesis (i.e. variable type declaration)
  <label> $e ... $. - "Essential" hypothesis (i.e. a logical assumption for a
                      theorem or axiom)
  <label> $a ... $. - Axiom or definition or syntax construction
  <label> $p ... $= ... $. - Theorem and its proof
          ${ ... $} - Block for defining the scope of the above statements
                      (except $a, $p which are forever active)
$)        $( ... $)
$(                  - Comments (may not be nested); see HELP LANGUAGE
                      for markup features
          $[ ... $] - Include a file

The above two-character sequences beginning with "$" are the only primitives
built into the Metamath language.  The only "logic" Metamath uses in its proof
verification algorithm is the substitution of expressions for variables while
checking for distinct variable violations.  Everything else, including the
axioms for logic, is defined in this database file.

Here is some more detail about the syntax.  There are two kinds of user-defined
syntax elements, called math symbols (or just symbols) and labels.  A symbol
may contain any non-whitespace printable character except "$".  A label may
contain only alphanumeric characters and the characters "."  (period), "-"
(hyphen), and "_" (underscore).  Tokens and labels are case-sensitive.  All
labels (except in proofs) must be distinct.  A label may not have the same name
as a token (to simplify the coding of certain parsers and translators).

  $c <symbollist> $.
      <symbollist> is a (whitespace-separated) list of distinct symbols that
      haven't been used before.
  $v <symbollist> $.
      <symbollist> is a list of distinct symbols that haven't been used yet
      in the current scope (see ${ ... $} below).
  $d <symbollist> $.
      <symbollist> is a (whitespace-separated) list of distinct symbols
      previously declared with $v in current scope.  It means that
      substitutions into these symbols may not have variables in common.
  <label> $f <symbollist> $.
      <symbollist> is a list of 2 symbols, the first of which must be
      previously declared with $c in the current scope.
  <label> $e <symbollist> $.
      <symbollist> is a list of 2 or more symbols, the first of which must be
      previously declared with $c in the current scope.
  <label> $a <symbollist> $.
      <symbollist> is a list of 2 or more symbols, the first of which must be
      previously declared with $c in the current scope.
  <label> $p <symbollist> $= <proof> $.
      <symbollist> is a list of 2 or more symbols, the first of which must be
      previously declared with $c in the current scope.  <proof> is either a
      whitespace-delimited sequence of previous labels (created by
      SAVE PROOF <label> /NORMAL) or a compressed proof (created by
      SAVE PROOF <label> /COMPRESSED).  After using SAVE PROOF, use
      WRITE SOURCE to save the database file to disk.
  ${ ... $}
      Block for scoping the above statements (except $a, $p which are forever
      active).  Currently, $c may not occur inside of a block.
$)
  $( <any text> $)
$(    Comment.  Note: <any text> may not contain adjacent "$" and ")"
      characters.
  $[ <filename> $]
      Insert contents of <filename> at this point.  If <filename> is current
      file or has been already been inserted, it will not be inserted again.

Inside of comments, it is recommended that labels be preceded with a tilde (~)
and math symbol tokens be enclosed in grave accents (` `).  This way the LaTeX
and HTML rendition of comments will be accurate, and (future) tools to globally
change labels and math symbols will also change them in comments.  Note that ``
inside of grave accents is interpreted as a single ` .  A special comment
containing $ t defines LaTeX and HTML symbols.  See HELP LANGUAGE and
HELP HTML for other markup features in comments.

The proofs in this file are in "compressed" format for storage efficiency.  The
Metamath program reads the compressed format directly.  This format is
described in an Appendix of the Metamath book.  It is not intended to be read
by humans.  For viewing proofs you should use the various SHOW PROOF commands
described in the Metamath book (or the on-line HELP).

The Metamath program does not normally affect any content of this file (set.mm)
other than proofs, i.e. tokens between "$=" and "$.".  All other content is
user-created.  Proofs are created or modified with the PROVE command.


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          5. Other notes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

1. It is recommended that you be familiar with chapters 2 and 4 of the
'Metamath' book to understand the Metamath language.  Chapters 2, 3 and 5
explain how to use the program.  Chapter 3 gives you an informal overview of
what this source file is all about.  Appendix A shows you the standard
mathematical symbols corresponding to some of the ASCII tokens in this file.

The ASCII tokens may seem cryptic at first, even if you are familiar with set
theory, but a review of the definition summary in Chapter 3 should quickly
enable you to see the correspondence to standard mathematical notation.  To
easily find the definition of a token, search for the first occurrences of the
token surrounded by spaces.  Some odd-looking ones include "-." for "not", and
"C_" for "is a subset of."  (HELP TEX tells you how to obtain a LaTeX output to
see the real mathematical symbols.)  Let me know if you have better suggestions
for naming ASCII tokens.

2. Logic and set theory provide a foundation for all of mathematics.  To learn
about them, you should study one or more of the references listed below.  The
textbooks provide a motivation for what we are doing, whereas Metamath lets you
see in detail all hidden and implicit steps.  Most standard theorems are
accompanied by citations.  Some closely followed texts include the following:

  Axioms of propositional calculus - [Margaris].
  Axioms of predicate calculus - [Megill] (System S3' in the article
      referenced).
  Theorems of propositional calculus - [WhiteheadRussell].
  Theorems of pure predicate calculus - [Margaris].
  Theorems of equality and substitution - [Monk2], [Tarski], [Megill].
  Axioms of set theory - [BellMachover].
  Development of set theory - [TakeutiZaring].  (The first part of [Quine]
      has a good explanation of the powerful device of "virtual" or
      class abstractions, which is essential to our development.)
  Construction of real and complex numbers - [Gleason]
  Theorems about real numbers - [Apostol]

3. Convention:  All $a statements starting with "|-" have labels
starting with "ax-" (axioms) or "df-" (definitions).  "ax-" corresponds
to what is traditionally called an axiom.  "df-" introduces new symbols
or a new relationship among symbols that can be eliminated; they always
extend the definition of a wff or class.  Metamath blindly treats $a
statements as new given facts but does not try to justify them.  The
mmj2 program will justify the definitions as sound, except for 5 (df-bi,
df-cleq, df-clel, df-clab, df-sbc) that require a more complex metalogical
justification by hand.

4. Our method of definition, the axioms for predicate calculus, and the
development of substitution are somewhat different from those found in standard
texts.  The axioms were designed for direct derivation of standard results
without excessive use of metatheorems.  (See Theorem 9.7 of [Megill] for a
rigorous justification.)  Typically we are minimalist when introducing new
definitions; they are introduced only when a clear advantage becomes apparent
for reducing the number of symbols, shortening proofs, etc.  We generally avoid
the introduction of gratuitous definitions because each one requires associated
theorems and additional elimination steps in proofs.

5. Where possible, the notation attempts to conform to modern conventions, with
variations due to our choice of the axiom system or to make proofs shorter.
Listed below are some important conventions and how they correspond to textbook
language.  The notation is usually explained in more detail when first
introduced.

  Typically, Greek letters (ph = phi, ps = psi, ch = chi, etc.) are used for
      propositional (wff) variables; x,y,z,... for individual (i.e. set)
      variables; and A,B,C,... for class variables.
  "|-", meaning "It is provable that," is the first token of all assertions
      and hypotheses that aren't syntax constructions.  This is a standard
      convention in logic.  For us, it also prevents any ambiguity with
      statements that are syntax constructions, such as "wff -. ph".
  "$e |- ( ph -> A. x ph ) $." should be read "Assume variable x is
      (effectively) not free in wff phi."  Literally, this says "Assume it is
      provable that phi implies for all x phi."
  "|- ( -. A. x x = y -> ..." should be read "If x and y are distinct
      variables, then..."  This antecedent provides us with a technical
      device (called a "distinctor" in [Megill]) to avoid the need for the
      $d statement early in our development of predicate calculus, permitting
      unrestricted substitituions as conceptually simple as those in
      propositional calculus.  However, the $d eventually becomes a
      requirement, and after that this device is rarely used.
  "[ y / x ] ph" should be read "the wff that results when y is properly
      substituted for x in ph."
  "$d x y $." should be read "Assume x and y are distinct variables."
  "$d x ph $." should be read "Assume x does not occur in phi $."  Sometimes
      a theorem is proved with "$e |- ( ph -> A. x ph ) $." in place of
      "$d x ph $." when a more general result is desired; ~ ax-17 can be used
      to derive the $d version.  For an example of how to get from the $d
      version back to the $e version, see the proof of ~ euf from ~ df-eu .
  "$d x A $." should be read "Assume x is not a variable occurring in class A."
  "$d x A $.  $d x ps $.  $e |- ( x = A -> ( ph <-> ps ) ) $." is an idiom
      often used instead of explicit substitution, meaning "Assume psi results
      from the substitution of A for x in phi."
  "$e |- A e. _V $." should be read "Assume class A is a set (i.e. exists)."
      This is a convenient convention used by [Quine].
  "$d x y $.  $e |- y e. A -> A. x y e. A $." should be read "Assume x is
      (effectively) not a free variable in class A."
  "`' R" should be read "converse of (relation) R" and is the same as the more
      standard notation R^{-1}.
  "( f ` x )" should be read "the value of function f at x" and is the same as
      the more familiar f(x).
  The Deduction Theorem of standard logic is never used.  Instead, in set
      theory, we use other tricks to make a $e hypothesis become an antecedent.
      See the comment for theorem ~ dedth below.


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           6. Acceptable shorter proofs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Shorter proofs are welcome, and any shorter proof I accept will be acknowledged
in the theorem's description.  However, in some cases a proof may be "shorter"
or not depending on how it is formatted.  This section provides general
guidelines.

Usually I will automatically accept shorter proofs that (1) shorten the set.mm
file (with compressed proofs), (2) reduce the size of the HTML file generated
with SHOW STATEMENT xx / HTML, (3) use only existing, unmodified theorems in
the database (the order of theorems may be changed, though), and (4) use no
additional axioms.

Usually I will also automatically accept a _new_ theorem that is used to
shorten multiple proofs, if the total size of set.mm (including the comment of
the new theorem, not including the acknowledgment) decreases as a result.

In borderline cases, I typically place more importance on the number of
compressed proof steps and less on the length of the label section (since the
names are in principal arbitrary).  If two proofs have the same number of
compressed proof steps, I will typically give preference to the one with the
smaller number of different labels, or if these numbers are the same, the proof
with the fewest number of characters that the proofs happen to have by chance
when label lengths are included.

A few theorems have a longer proof than necessary in order to avoid the use of
certain axioms, for pedagogical purposes, and for other reasons.  Usually this
is clear from the theorem's description.  For example, id1 shows a proof
directly from axioms.  Shorter proofs for such cases won't be accepted, of
course, unless the criteria described continues to be satisfied.

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Future:  ideas for possible axiom renaming
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

     old    possible new name(s)          description

     ax-1   ax-k     Axiom Simp (principal type scheme for combinator K)
     ax-2   ax-s     Axiom Frege (principal type scheme for combinator S)
     ax-3   ax-t     Axiom Transp
     ax-mp  ax-mp    Rule of Modus Ponens

     ax-5   ax-qim  ax-qi  ax-q1  ax-4   Axiom of Quantified Implication
     ax-6   ax-qne  ax-qn  ax-q2  ax-5   Axiom of Quantified Negation
     ax-7   ax-qqc  ax-qq  ax-q3  ax-6   Axiom of Quantifier Commutation
     ax-gen ax-gen  ax-gen        ax-gen Rule of Generalization
     ax-8   ax-eq1  ax-e1  ax-e1  ax-7   Axiom of Equality (1)
     ax-9   ax-exi  ax-ex  ax-e2  ax-8   Axiom of Existence
     ax-10  ax-sbq  ax-qs  ax-e3  ax-9   Axiom of Quantifier Substitution
     ax-11  ax-sbv  ax-vs  ax-e4  ax-10  Axiom of Variable Substitution
     ax-12  ax-qi1  ax-qe  ax-e5  ax-11  Axiom of Quantifier Introduction (1)
     ax-13  ax-eq2  ax-e2  ax-e6  ax-12  Axiom of Equality (2)
     ax-14  ax-eq3  ax-e3  ax-e7  ax-13  Axiom of Equality (3)
     ax-17  ax-qi2  ax-qi  ax-qi  ax-14  Axiom of Quantifier Introduction (2)

     obsolete versions or redundant:
     ax-4   ax-spc  ax-sp  ax-q4  ax-15  Axiom of Specialization
     ax-5o  ax-qimo ax-qio ax-q5  ax-4o  Axiom of Quantified Implication
     ax-6o  ax-qneo ax-qno ax-q6  ax-5o  Axiom of Quantified Negation
     ax-9o  ax-exio ax-exo ax-e8  ax-8o  Axiom of Existence
     ax-10o ax-sbqo ax-sqo ax-e9  ax-9o  Axiom of Quantifier Substitution
     ax-11o ax-sbvo ax-svo ax-e10 ax-10o Axiom of Variable Substitution
     ax-15  ax-qi3  ax-q3  ax-e11 ax-16  Axiom of Quantifier Introduction
     ax-16  ax-qi4  ax-dv  ax-e12 ax-17  Axiom of Distinct Variables
$)


$(
###############################################################################
            CLASSICAL FIRST ORDER LOGIC WITH EQUALITY
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
              'a proof exists for") $)

  $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)
  $v et $.  $( Greek eta $)
  $v ze $.  $( Greek zeta $)
  $v si $.  $( Greek sigma $)
  $v rh $.  $( Greek rho $)
  $v mu $.  $( Greek mu $)
  $v la $.  $( Greek lambda $)
  $v ka $.  $( Greek kappa $)

  $( Specify some variables that we will use to represent wff's.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` wff ` specifies that the variable that follows it represents a wff. $)
  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.
  $( Let variable ` ta ` be a wff. $)
  wta $f wff ta $.
  $( Let variable ` et ` be a wff. $)
  wet $f wff et $.
  $( Let variable ` ze ` be a wff. $)
  wze $f wff ze $.
  $( Let variable ` si ` be a wff. $)
  wsi $f wff si $.
  $( Let variable ` rh ` be a wff. $)
  wrh $f wff rh $.
  $( Let variable ` mu ` be a wff. $)
  wmu $f wff mu $.
  $( Let variable ` la ` be a wff. $)
  wla $f wff la $.
  $( Let variable ` ka ` be a wff. $)
  wka $f wff ka $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Inferences for assisting proof development
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    dummylink.1 $e |- ph $.
    dummylink.2 $e |- ps $.
    $( (_Note_:  This inference rule and the next one, ~ idi , will normally
       never appear in a completed proof.  It can be ignored if you are using
       this database to assist learning logic - please start with the statement
       ~ wn instead.)

       This is a technical inference to assist proof development.  It provides
       a temporary way to add an independent subproof to a proof under
       development, for later assignment to a normal proof step.

       The metamath program's Proof Assistant requires proofs to be developed
       backwards from the conclusion with no gaps, and it has no mechanism that
       lets the user to work on isolated subproofs.  This inference provides a
       workaround for this limitation.  It can be inserted at any point in a
       proof to allow an independent subproof to be developed on the side, for
       later use as part of the final proof.

       _Instructions_:  (1) Assign this inference to any unknown step in the
       proof.  Typically, the last unknown step is the most convenient, since
       'assign last' can be used.  This step will be replicated in hypothesis
       dummylink.1, from where the development of the main proof can continue.
       (2) Develop the independent subproof backwards from hypothesis
       dummylink.2.  If desired, use a 'let' command to pre-assign the
       conclusion of the independent subproof to dummylink.2.  (3) After the
       independent subproof is complete, use 'improve all' to assign it
       automatically to an unknown step in the main proof that matches it.  (4)
       After the entire proof is complete, use 'minimize *' to clean up
       (discard) all dummylink references automatically.

       This inference was originally designed to assist importing partially
       completed Proof Worksheets from the mmj2 Proof Assistant GUI, but it can
       also be useful on its own.  Interestingly, no axioms are required for
       its proof. $)
    dummylink $p |- ph $=
      (  ) C $.
      $( [7-Feb-2006] $)
  $}

  ${
    idi.1 $e |- ph $.
    $( Inference form of ~ id .  This inference rule, which requires no axioms
       for its proof, is useful as a copy-paste mechanism during proof
       development in mmj2.  It is normally not referenced in the final version
       of a proof, since it is always redundant and can be removed using the
       'minimize *' command in the metamath program's Proof Assistant.
       (Contributed by Alan Sare, 31-Dec-2011.) $)
    idi $p |- ph $=
      (  ) B $.
      $( [31-Dec-2011] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Recursively define primitive wffs for propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If ` ph ` is a wff, so is ` -. ph ` or "not ` ph ` ."  Part of the
     recursive definition of a wff (well-formed formula).  In classical logic
     (which is our logic), a wff is interpreted as either true or false.  So if
     ` ph ` is true, then ` -. ph ` is false; if ` ph ` is false, then
     ` -. ph ` is true.  Traditionally, Greek letters are used to represent
     wffs, and we follow this convention.  In propositional calculus, we define
     only wffs built up from other wffs, i.e. there is no starting or "atomic"
     wff.  Later, in predicate calculus, we will extend the basic wff
     definition by including atomic wffs ( ~ weq and ~ wel ). $)
  wn $a wff -. ph $.

  $( If ` ph ` and ` ps ` are wff's, so is ` ( ph -> ps ) ` or " ` ph ` implies
     ` ps ` ."  Part of the recursive definition of a wff.  The resulting wff
     is (interpreted as) false when ` ph ` is true and ` ps ` is false; it is
     true otherwise.  (Think of the truth table for an OR gate with input
     ` ph ` connected through an inverter.)  The left-hand wff is called the
     antecedent, and the right-hand wff is called the consequent.  In the case
     of ` ( ph -> ( ps -> ch ) ) ` , the middle ` ps ` may be informally called
     either an antecedent or part of the consequent depending on context. $)
  wi $a wff ( ph -> ps ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The axioms of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $(
     Postulate the three axioms of classical propositional calculus.
  $)

  $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  The 3 axioms are also given as Definition 2.1 of
     [Hamilton] p. 28.  This axiom is called _Simp_ or "the principle of
     simplification" in _Principia Mathematica_ (Theorem *2.02 of
     [WhiteheadRussell] p. 100) because "it enables us to pass from the joint
     assertion of ` ph ` and ` ps ` to the assertion of ` ph ` simply."

     _General remarks_:  Propositional calculus (axioms ~ ax-1 through ~ ax-3
     and rule ~ ax-mp ) can be thought of as asserting formulas that are
     universally "true" when their variables are replaced by any combination of
     "true" and "false."  Propositional calculus was first formalized by Frege
     in 1879, using as his axioms (in addition to rule ~ ax-mp ) the wffs
     ~ ax-1 , ~ ax-2 , ~ pm2.04 , ~ con3 , ~ notnot2 , and ~ notnot1 .  Around
     1930, Lukasiewicz simplified the system by eliminating the third (which
     follows from the first two, as you can see by looking at the proof of
     ~ pm2.04 ) and replacing the last three with our ~ ax-3 .  (Thanks to Ted
     Ulrich for this information.)

     The theorems of propositional calculus are also called _tautologies_.
     Tautologies can be proved very simply using truth tables, based on the
     true/false interpretation of propositional calculus.  To do this, we
     assign all possible combinations of true and false to the wff variables
     and verify that the result (using the rules described in ~ wi and ~ wn )
     always evaluates to true.  This is called the _semantic_ approach.  Our
     approach is called the _syntactic_ approach, in which everything is
     derived from axioms.  A metatheorem called the Completeness Theorem for
     Propositional Calculus shows that the two approaches are equivalent and
     even provides an algorithm for automatically generating syntactic proofs
     from a truth table.  Those proofs, however, tend to be long, since truth
     tables grow exponentially with the number of variables, and the much
     shorter proofs that we show here were found manually. $)
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

  $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It "distributes" an antecedent over two
     consequents.  This axiom was part of Frege's original system and is known
     as _Frege_ in the literature.  It is also proved as Theorem *2.77 of
     [WhiteheadRussell] p. 108.  The other direction of this axiom also turns
     out to be true, as demonstrated by ~ pm5.41 . $)
  ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

  $( Axiom _Transp_.  Axiom A3 of [Margaris] p. 49.  One of the 3 axioms of
     propositional calculus.  It swaps or "transposes" the order of the
     consequents when negation is removed.  An informal example is that the
     statement "if there are no clouds in the sky, it is not raining" implies
     the statement "if it is raining, there are clouds in the sky."  This axiom
     is called _Transp_ or "the principle of transposition" in _Principia
     Mathematica_ (Theorem *2.17 of [WhiteheadRussell] p. 103).  We will also
     use the term "contraposition" for this principle, although the reader is
     advised that in the field of philosophical logic, "contraposition" has a
     different technical meaning. $)
  ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

  $(
     Postulate the modus ponens rule of inference.
  $)

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See e.g.  Rule 1 of [Hamilton] p. 73.  The rule says, "if
       ` ph ` is true, and ` ph ` implies ` ps ` , then ` ps ` must also be
       true."  This rule is sometimes called "detachment," since it detaches
       the minor premise from the major premise.

       Note:  In some web page displays such as the Statement List, the symbols
       "&" and "=>" informally indicate the relationship between the hypotheses
       and the assertion (conclusion), abbreviating the English words "and" and
       "implies."  They are not part of the formal language. $)
    ax-mp $a |- ps $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( The results in this section are based on implication only, and avoid ax-3.
   In an implication, the wff before the arrow is called the "antecedent" and
   the wff after the arrow is called the "consequent." $)

$( We will use the following descriptive terms very loosely:  A "closed form"
   or "tautology" has no $e hypotheses.  An "inference" has one or more $e
   hypotheses.  A "deduction" is an inference in which the hypotheses and the
   conclusion share the same antecedent. $)

  ${
    mp2b.1 $e |- ph $.
    mp2b.2 $e |- ( ph -> ps ) $.
    mp2b.3 $e |- ( ps -> ch ) $.
    $( A double modus ponens inference.  (Contributed by Mario Carneiro,
       24-Jan-2013.) $)
    mp2b $p |- ch $=
      ( ax-mp ) BCABDEGFG $.
      $( [24-Jan-2013] $)
  $}

  ${
    $( Premise for ~ a1i . $)
    a1i.1 $e |- ph $.
    $( Inference derived from axiom ~ ax-1 .  See ~ a1d for an explanation of
       our informal use of the terms "inference" and "deduction."  See also the
       comment in ~ syld . $)
    a1i $p |- ( ps -> ph ) $=
      ( wi ax-1 ax-mp ) ABADCABEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    $( Premise for ~ a2i . $)
    a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference derived from axiom ~ ax-2 . $)
    a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
      ( wi ax-2 ax-mp ) ABCEEABEACEEDABCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    imim2i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common antecedents in an implication. $)
    imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
      ( wi a1i a2i ) CABABECDFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpd.1 $e |- ( ph -> ps ) $.
    mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A modus ponens deduction. $)
    mpd $p |- ( ph -> ch ) $=
      ( wi a2i ax-mp ) ABFACFDABCEGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    $( First of 2 premises for ~ syl . $)
    syl.1 $e |- ( ph -> ps ) $.
    $( Second of 2 premises for ~ syl . $)
    syl.2 $e |- ( ps -> ch ) $.
    $( An inference version of the transitive laws for implication ~ imim2 and
       ~ imim1 , which Russell and Whitehead call "the principle of the
       syllogism...because...the syllogism in Barbara is derived from them"
       (quote after Theorem *2.06 of [WhiteheadRussell] p. 101).  Some authors
       call this law a "hypothetical syllogism."  (The proof was shortened by
       O'Cat, 20-Oct-2011.)  (The proof was shortened by Wolf Lammen,
       26-Jul-2012.) $)
    syl $p |- ( ph -> ch ) $=
      ( wi a1i mpd ) ABCDBCFAEGH $.
      $( [27-Jul-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    mpi.1 $e |- ps $.
    mpi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A nested modus ponens inference.  (The proof was shortened by Stefan
       Allan, 20-Mar-2006.) $)
    mpi $p |- ( ph -> ch ) $=
      ( a1i mpd ) ABCBADFEG $.
      $( [20-Mar-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    mp2.1 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A double modus ponens inference.  (The proof was shortened by Wolf
       Lammen, 23-Jul-2013.) $)
    mp2 $p |- ch $=
      ( mpi ax-mp ) ACDABCEFGH $.
      $( [23-Jul-2013] $) $( [5-Apr-1994] $)
  $}

  ${
    3syl.1 $e |- ( ph -> ps ) $.
    3syl.2 $e |- ( ps -> ch ) $.
    3syl.3 $e |- ( ch -> th ) $.
    $( Inference chaining two syllogisms. $)
    3syl $p |- ( ph -> th ) $=
      ( syl ) ACDABCEFHGH $.
      $( [5-Aug-1993] $)
  $}

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  For
     another version of the proof directly from axioms, see ~ id1 .  (The proof
     was shortened by Stefan Allan, 20-Mar-2006.) $)
  id $p |- ( ph -> ph ) $=
    ( wi ax-1 mpd ) AAABZAAACAECD $.
    $( [20-Mar-2006] $)

  $( Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.  This
     version is proved directly from the axioms for demonstration purposes.
     This proof is a popular example in the literature and is identical, step
     for step, to the proofs of Theorem 1 of [Margaris] p. 51, Example 2.7(a)
     of [Hamilton] p. 31, Lemma 10.3 of [BellMachover] p. 36, and Lemma 1.8 of
     [Mendelson] p. 36.  It is also "Our first proof" in Hirst and Hirst's _A
     Primer for Logic and Proof_ p. 17 (PDF p. 23) at
     ~ http://www.mathsci.appstate.edu/~~jlh/primer/hirst.pdf .  For a shorter
     version of the proof that takes advantage of previously proved theorems,
     see ~ id . $)
  id1 $p |- ( ph -> ph ) $=
    ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.
    $( [5-Aug-1993] $)

  $( Principle of identity with antecedent. $)
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi id a1i ) BBCABDE $.
    $( [26-Nov-1995] $)

  ${
    a1d.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing an embedded antecedent.  (The proof was revised by
       Stefan Allan, 20-Mar-2006.)

       _Naming convention_:  We often call a theorem a "deduction" and suffix
       its label with "d" whenever the hypotheses and conclusion are each
       prefixed with the same antecedent.  This allows us to use the theorem in
       places where (in traditional textbook formalizations) the standard
       Deduction Theorem would be used; here ` ph ` would be replaced with a
       conjunction ( ~ df-an ) of the hypotheses of the would-be deduction.  By
       contrast, we tend to call the simpler version with no common antecedent
       an "inference" and suffix its label with "i"; compare theorem ~ a1i .
       Finally, a "theorem" would be the form with no hypotheses; in this case
       the "theorem" form would be the original axiom ~ ax-1 .  We usually show
       the theorem form without a suffix on its label (e.g. ~ pm2.43 vs.
       ~ pm2.43i vs. ~ pm2.43d ). $)
    a1d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wi ax-1 syl ) ABCBEDBCFG $.
      $( [20-Mar-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    a2d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Deduction distributing an embedded antecedent. $)
    a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
      ( wi ax-2 syl ) ABCDFFBCFBDFFEBCDGH $.
      $( [23-Jun-1994] $)
  $}

  ${
    a1ii.1 $e |- ch $.
    $( Add two antecedents to a wff.  (Contributed by Jeff Hankins,
       4-Aug-2009.)  (The proof was shortened by Wolf Lammen, 23-Jul-2013.) $)
    a1ii $p |- ( ph -> ( ps -> ch ) ) $=
      ( a1i a1d ) ACBCADEF $.
      $( [23-Jul-2013] $) $( [4-Aug-2009] $)
  $}

  ${
    sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
    $( Syllogism inference with commutation of antecedents.  (The proof was
       shortened by O'Cat, 2-Feb-2006.)  (The proof was shortened by Stefan
       Allan, 23-Feb-2006.) $)
    sylcom $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a2i syl ) ABCGBDGEBCDFHI $.
      $( [23-Feb-2006] $) $( [29-Aug-2004] $)
  $}

  ${
    syl5com.1 $e |- ( ph -> ps ) $.
    syl5com.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Syllogism inference with commuted antecedents. $)
    syl5com $p |- ( ph -> ( ch -> th ) ) $=
      ( a1d sylcom ) ACBDABCEGFH $.
      $( [24-May-2005] $)
  $}

  ${
    $( Premise for ~ com12 .  See ~ pm2.04 for the theorem form. $)
    com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference that swaps (commutes) antecedents in an implication.  (The
       proof was shortened by Wolf Lammen, 4-Aug-2012.) $)
    com12 $p |- ( ps -> ( ph -> ch ) ) $=
      ( id syl5com ) BBACBEDF $.
      $( [4-Aug-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    syl5.1 $e |- ( ph -> ps ) $.
    syl5.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the second antecedent of the first premise.  (The proof was shortened by
       Wolf Lammen, 25-May-2013.) $)
    syl5 $p |- ( ch -> ( ph -> th ) ) $=
      ( syl5com com12 ) ACDABCDEFGH $.
      $( [25-May-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6.2 $e |- ( ch -> th ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (The proof was shortened by Wolf
       Lammen, 30-Jul-2012.) $)
    syl6 $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1i sylcom ) ABCDECDGBFHI $.
      $( [31-Jul-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    syl56.1 $e |- ( ph -> ps ) $.
    syl56.2 $e |- ( ch -> ( ps -> th ) ) $.
    syl56.3 $e |- ( th -> ta ) $.
    $( Combine ~ syl5 and ~ syl6 . $)
    syl56 $p |- ( ch -> ( ph -> ta ) ) $=
      ( syl6 syl5 ) ABCEFCBDEGHIJ $.
      $( [14-Nov-2013] $)
  $}

  ${
    syl6com.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6com.2 $e |- ( ch -> th ) $.
    $( Syllogism inference with commuted antecedents. $)
    syl6com $p |- ( ps -> ( ph -> th ) ) $=
      ( syl6 com12 ) ABDABCDEFGH $.
      $( [25-May-2005] $)
  $}

  ${
    mpcom.1 $e |- ( ps -> ph ) $.
    mpcom.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus ponens inference with commutation of antecedents. $)
    mpcom $p |- ( ps -> ch ) $=
      ( com12 mpd ) BACDABCEFG $.
      $( [17-Mar-1996] $)
  $}

  ${
    syli.1 $e |- ( ps -> ( ph -> ch ) ) $.
    syli.2 $e |- ( ch -> ( ph -> th ) ) $.
    $( Syllogism inference with common nested antecedent. $)
    syli $p |- ( ps -> ( ph -> th ) ) $=
      ( com12 sylcom ) BACDECADFGH $.
      $( [4-Nov-2004] $)
  $}

  ${
    syl2im.1 $e |- ( ph -> ps ) $.
    syl2im.2 $e |- ( ch -> th ) $.
    syl2im.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( Replace two antecedents.  Implication-only version of ~ syl2an .
       (Contributed by Wolf Lammen, 14-May-2013.) $)
    syl2im $p |- ( ph -> ( ch -> ta ) ) $=
      ( wi syl5 syl ) ABCEIFCDBEGHJK $.
      $( [14-May-2013] $)
  $}

  $( This theorem, called "Assertion," can be thought of as closed form of
     modus ponens ~ ax-mp .  Theorem *2.27 of [WhiteheadRussell] p. 104. $)
  pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi id com12 ) ABCZABFDE $.
    $( [5-Aug-1993] $)

  ${
    mpdd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    mpdd.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction. $)
    mpdd $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a2d mpd ) ABCGBDGEABCDFHI $.
      $( [12-Dec-2004] $)
  $}

  ${
    mpid.1 $e |- ( ph -> ch ) $.
    mpid.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction. $)
    mpid $p |- ( ph -> ( ps -> th ) ) $=
      ( a1d mpdd ) ABCDACBEGFH $.
      $( [14-Dec-2004] $)
  $}

  ${
    mpdi.1 $e |- ( ps -> ch ) $.
    mpdi.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A nested modus ponens deduction.  (The proof was shortened by O'Cat,
       15-Jan-2008.) $)
    mpdi $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1i mpdd ) ABCDBCGAEHFI $.
      $( [15-Jan-2008] $) $( [16-Apr-2005] $)
  $}

  ${
    mpii.1 $e |- ch $.
    mpii.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A doubly nested modus ponens inference.  (The proof was shortened by
       Wolf Lammen, 31-Jul-2012.) $)
    mpii $p |- ( ph -> ( ps -> th ) ) $=
      ( a1i mpdi ) ABCDCBEGFH $.
      $( [31-Jul-2012] $) $( [31-Dec-1993] $)
  $}

  ${
    syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Syllogism deduction.  (The proof was shortened by O'Cat, 19-Feb-2008.)
       (The proof was shortened by Wolf Lammen, 3-Aug-2012.)

       Notice that ~ syld has the same form as ~ syl with ` ph ` added in front
       of each hypothesis and conclusion.  When all theorems referenced in a
       proof are converted in this way, we can replace ` ph ` with a hypothesis
       of the proof, allowing the hypothesis to be eliminated with ~ id and
       become an antecedent.  The Deduction Theorem for propositional calculus,
       e.g.  Theorem 3 in [Margaris] p. 56, tells us that this procedure is
       always possible. $)
    syld $p |- ( ph -> ( ps -> th ) ) $=
      ( wi a1d mpdd ) ABCDEACDGBFHI $.
      $( [3-Aug-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    mp2d.1 $e |- ( ph -> ps ) $.
    mp2d.2 $e |- ( ph -> ch ) $.
    mp2d.3 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A double modus ponens deduction.  (The proof was shortened by Wolf
       Lammen, 23-Jul-2013.) $)
    mp2d $p |- ( ph -> th ) $=
      ( mpid mpd ) ABDEABCDFGHI $.
      $( [23-Jul-2013] $) $( [23-May-2013] $)
  $}

  ${
    a1dd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction introducing a nested embedded antecedent.  (The proof was
       shortened by O'Cat, 15-Jan-2008.) $)
    a1dd $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      ( wi ax-1 syl6 ) ABCDCFECDGH $.
      $( [15-Jan-2008] $) $( [17-Dec-2004] $)
  $}

  ${
    pm2.43i.1 $e |- ( ph -> ( ph -> ps ) ) $.
    $( Inference absorbing redundant antecedent.  (The proof was shortened by
       O'Cat, 28-Nov-2008.) $)
    pm2.43i $p |- ( ph -> ps ) $=
      ( id mpd ) AABADCE $.
      $( [29-Nov-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    pm2.43d.1 $e |- ( ph -> ( ps -> ( ps -> ch ) ) ) $.
    $( Deduction absorbing redundant antecedent.  (The proof was shortened by
       O'Cat, 28-Nov-2008.) $)
    pm2.43d $p |- ( ph -> ( ps -> ch ) ) $=
      ( id mpdi ) ABBCBEDF $.
      $( [29-Nov-2008] $) $( [18-Aug-1993] $)
  $}

  ${
    pm2.43a.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent.  (The proof was shortened by
       O'Cat, 28-Nov-2008.) $)
    pm2.43a $p |- ( ps -> ( ph -> ch ) ) $=
      ( id mpid ) BABCBEDF $.
      $( [29-Nov-2008] $) $( [7-Nov-1995] $)
  $}

  ${
    pm2.43b.1 $e |- ( ps -> ( ph -> ( ps -> ch ) ) ) $.
    $( Inference absorbing redundant antecedent. $)
    pm2.43b $p |- ( ph -> ( ps -> ch ) ) $=
      ( pm2.43a com12 ) BACABCDEF $.
      $( [31-Oct-1995] $)
  $}

  $( Absorption of redundant antecedent.  Also called the "Contraction" or
     "Hilbert" axiom.  Theorem *2.43 of [WhiteheadRussell] p. 106.  (The proof
     was shortened by O'Cat, 15-Aug-2004.) $)
  pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi pm2.27 a2i ) AABCBABDE $.
    $( [15-Aug-2004] $) $( [5-Aug-1993] $)

  ${
    imim2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested antecedents. $)
    imim2d $p |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      ( wi a1d a2d ) ADBCABCFDEGH $.
      $( [5-Aug-1993] $)
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
     [WhiteheadRussell] p. 100.  (The proof was shortened by Wolf Lammen,
     6-Sep-2012.) $)
  imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi id imim2d ) ABDZABCGEF $.
    $( [6-Sep-2012] $) $( [5-Aug-1993] $)

  ${
    embantd.1 $e |- ( ph -> ps ) $.
    embantd.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction embedding an antecedent.  (Contributed by Wolf Lammen,
       4-Oct-2013.) $)
    embantd $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      ( wi imim2d mpid ) ABCGBDEACDBFHI $.
      $( [15-Jan-2014] $) $( [4-Oct-2013] $)
  $}

  ${
    3syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    3syld.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( Triple syllogism deduction.  (Contributed by Jeff Hankins,
       4-Aug-2009.) $)
    3syld $p |- ( ph -> ( ps -> ta ) ) $=
      ( syld ) ABDEABCDFGIHI $.
      $( [24-Sep-2010] $) $( [4-Aug-2009] $)
  $}

  ${
    sylsyld.1 $e |- ( ph -> ps ) $.
    sylsyld.2 $e |- ( ph -> ( ch -> th ) ) $.
    sylsyld.3 $e |- ( ps -> ( th -> ta ) ) $.
    $( Virtual deduction rule.
       (Contributed by Alan Sare, 20-Apr-2011.) $)
    sylsyld $p |- ( ph -> ( ch -> ta ) ) $=
      ( wi syl syld ) ACDEGABDEIFHJK $.
      $( [20-Apr-2011] $)
  $}

  ${
    imim12i.1 $e |- ( ph -> ps ) $.
    imim12i.2 $e |- ( ch -> th ) $.
    $( Inference joining two implications.  (The proof was shortened by O'Cat,
       29-Oct-2011.) $)
    imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $=
      ( wi imim2i syl5 ) ABBCGDECDBFHI $.
      $( [29-Oct-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    imim1i.1 $e |- ( ph -> ps ) $.
    $( Inference adding common consequents in an implication, thereby
       interchanging the original antecedent and consequent.  (The proof was
       shortened by Wolf Lammen, 4-Aug-2012.) $)
    imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
      ( id imim12i ) ABCCDCEF $.
      $( [4-Aug-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    imim3i.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference adding three nested antecedents. $)
    imim3i $p |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) ) $=
      ( wi imim2i a2d ) DAFDBCABCFDEGH $.
      $( [19-Dec-2006] $)
  $}

  ${
    sylc.1 $e |- ( ph -> ps ) $.
    sylc.2 $e |- ( ph -> ch ) $.
    sylc.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( A syllogism inference combined with contraction. $)
    sylc $p |- ( ph -> th ) $=
      ( syl2im pm2.43i ) ADABACDEFGHI $.
      $( [13-Jul-2013] $) $( [4-May-1994] $)
  $}

  ${
    syl3c.1 $e |- ( ph -> ps ) $.
    syl3c.2 $e |- ( ph -> ch ) $.
    syl3c.3 $e |- ( ph -> th ) $.
    syl3c.4 $e |- ( ps -> ( ch -> ( th -> ta ) ) ) $.
    $( A syllogism inference combined with contraction.
       (Contributed by Alan Sare, 7-Jul-2011.) $)
    syl3c $p |- ( ph -> ta ) $=
      ( wi sylc mpd ) ADEHABCDEJFGIKL $.
      $( [7-Jul-2011] $)
  $}

  ${
    syl6mpi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6mpi.2 $e |- th $.
    syl6mpi.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( ~ syl6 combined with ~ mpi .  (Contributed by Alan Sare,
       8-Jul-2011.)  (The proof was shortened by Wolf Lammen, 13-Sep-2012.) $)
    syl6mpi $p |- ( ph -> ( ps -> ta ) ) $=
      ( mpi syl6 ) ABCEFCDEGHIJ $.
      $( [13-Sep-2012] $) $( [8-Jul-2011] $)
  $}

  ${
    mpsyl.1 $e |- ph $.
    mpsyl.2 $e |- ( ps -> ch ) $.
    mpsyl.3 $e |- ( ph -> ( ch -> th ) ) $.
    $( Modus ponens combined with a syllogism inference.  (Contributed by Alan
       Sare, 20-Apr-2011.) $)
    mpsyl $p |- ( ps -> th ) $=
      ( a1i sylc ) BACDABEHFGI $.
      $( [20-Apr-2011] $)
  $}

  ${
    syl6c.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6c.2 $e |- ( ph -> ( ps -> th ) ) $.
    syl6c.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Inference combining ~ syl6 with contraction.  (Contributed by Alan Sare,
       2-May-2011.) $)
    syl6c $p |- ( ph -> ( ps -> ta ) ) $=
      ( wi syl6 mpdd ) ABDEGABCDEIFHJK $.
      $( [2-May-2011] $)
  $}

  ${
    syldd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syldd.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    $( Nested syllogism deduction.  (The proof was shortened by Wolf Lammen,
       11-May-2013.) $)
    syldd $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi imim2 syl6c ) ABDEHCDHCEHGFDECIJ $.
      $( [11-May-2013] $) $( [12-Dec-2004] $)
  $}

  ${
    syl5d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl5d.2 $e |- ( ph -> ( th -> ( ch -> ta ) ) ) $.
    $( A nested syllogism deduction.  (The proof was shortened by Josh
       Purinton, 29-Dec-2000 and shortened further by O'Cat, 2-Feb-2006.) $)
    syl5d $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      ( wi a1d syldd ) ADBCEABCHDFIGJ $.
      $( [3-Feb-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    syl7.1 $e |- ( ph -> ps ) $.
    syl7.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the third antecedent of the first premise.  (The proof was shortened by
       Wolf Lammen, 3-Aug-2012.) $)
    syl7 $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      ( wi a1i syl5d ) CABDEABHCFIGJ $.
      $( [3-Aug-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    syl6d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl6d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( A nested syllogism deduction.  (The proof was shortened by Josh
       Purinton, 29-Dec-2000 and shortened further by O'Cat, 2-Feb-2006.) $)
    syl6d $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi a1d syldd ) ABCDEFADEHBGIJ $.
      $( [3-Feb-2006] $) $( [5-Aug-1993] $)
  $}

  ${
    syl8.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8.2 $e |- ( th -> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise.  (The proof was shortened by Wolf
       Lammen, 3-Aug-2012.) $)
    syl8 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi a1i syl6d ) ABCDEFDEHAGIJ $.
      $( [3-Aug-2012] $) $( [1-Aug-1994] $)
  $}

  ${
    syl9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents.  (The proof was
       shortened by Josh Purinton, 29-Dec-2000.) $)
    syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $=
      ( wi a1i syl5d ) ABCDEFDCEHHAGIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( A nested syllogism inference with different antecedents. $)
    syl9r $p |- ( th -> ( ph -> ( ps -> ta ) ) ) $=
      ( wi syl9 com12 ) ADBEHABCDEFGIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    imim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Deduction combining antecedents and consequents.  (The proof was
       shortened by O'Cat, 30-Oct-2011.) $)
    imim12d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) ) $=
      ( wi imim2d syl5d ) ABCCDHEFADECGIJ $.
      $( [3-Nov-2011] $) $( [7-Aug-1994] $)
  $}

  ${
    imim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding nested consequents.  (The proof was shortened by Wolf
       Lammen, 12-Sep-2012.) $)
    imim1d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) ) $=
      ( idd imim12d ) ABCDDEADFG $.
      $( [12-Sep-2012] $) $( [3-Apr-1994] $)
  $}

  $( A closed form of syllogism (see ~ syl ).  Theorem *2.06 of
     [WhiteheadRussell] p. 100.  (The proof was shortened by Wolf Lammen,
     25-May-2013.) $)
  imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi id imim1d ) ABDZABCGEF $.
    $( [25-May-2013] $) $( [5-Aug-1993] $)

  $( Theorem *2.83 of [WhiteheadRussell] p. 108. $)
  pm2.83 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ( ch -> th ) ) ->
                ( ph -> ( ps -> th ) ) ) ) $=
    ( wi imim1 imim3i ) BCECDEBDEABCDFG $.
    $( [3-Jan-2005] $)

  ${
    com3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Commutation of antecedents.  Swap 2nd and 3rd.  (The proof was shortened
       by Wolf Lammen, 4-Aug-2012.) $)
    com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      ( wi pm2.27 syl9 ) ABCDFCDECDGH $.
      $( [4-Aug-2012] $) $( [5-Aug-1993] $)

    $( Commutation of antecedents.  Rotate right. $)
    com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $=
      ( wi com23 com12 ) ACBDFABCDEGH $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Swap 1st and 3rd.  (The proof was shortened
       by Wolf Lammen, 28-Jul-2012.) $)
    com13 $p |- ( ch -> ( ps -> ( ph -> th ) ) ) $=
      ( com3r com23 ) CABDABCDEFG $.
      $( [28-Jul-2012] $) $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate left.  (The proof was shortened by
       Wolf Lammen, 28-Jul-2012.) $)
    com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      ( com3r ) CABDABCDEFF $.
      $( [28-Jul-2012] $) $( [25-Apr-1994] $)
  $}

  $( Swap antecedents.  Theorem *2.04 of [WhiteheadRussell] p. 100.  (The proof
     was shortened by Wolf Lammen, 12-Sep-2012.) $)
  pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi id com23 ) ABCDDZABCGEF $.
    $( [12-Sep-2012] $) $( [5-Aug-1993] $)

  ${
    com4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Commutation of antecedents.  Swap 3rd and 4th. $)
    com34 $p |- ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) $=
      ( wi pm2.04 syl6 ) ABCDEGGDCEGGFCDEHI $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate left.  (The proof was shortened by
       O'Cat, 15-Aug-2004.) $)
    com4l $p |- ( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) ) $=
      ( wi com3l com34 ) BCADEABCDEGFHI $.
      $( [15-Aug-2004] $) $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate twice. $)
    com4t $p |- ( ch -> ( th -> ( ph -> ( ps -> ta ) ) ) ) $=
      ( com4l ) BCDAEABCDEFGG $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Rotate right. $)
    com4r $p |- ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) $=
      ( com4t com4l ) CDABEABCDEFGH $.
      $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Swap 2nd and 4th.  (The proof was shortened
       by Wolf Lammen, 28-Jul-2012.) $)
    com24 $p |- ( ph -> ( th -> ( ch -> ( ps -> ta ) ) ) ) $=
      ( wi com4t com13 ) CDABEGABCDEFHI $.
      $( [28-Jul-2012] $) $( [25-Apr-1994] $)

    $( Commutation of antecedents.  Swap 1st and 4th.  (The proof was shortened
       by Wolf Lammen, 28-Jul-2012.) $)
    com14 $p |- ( th -> ( ps -> ( ch -> ( ph -> ta ) ) ) ) $=
      ( wi com4l com3r ) BCDAEGABCDEFHI $.
      $( [28-Jul-2012] $) $( [25-Apr-1994] $)
  $}

  ${
    com5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( Commutation of antecedents.  Swap 4th and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com45 $p |- ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) $=
      ( wi pm2.04 syl8 ) ABCDEFHHEDFHHGDEFIJ $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Swap 3rd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com35 $p |- ( ph -> ( ps -> ( ta -> ( th -> ( ch -> et ) ) ) ) ) $=
      ( wi com34 com45 ) ABDECFHABDCEFABCDEFHGIJI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Swap 2nd and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com25 $p |- ( ph -> ( ta -> ( ch -> ( th -> ( ps -> et ) ) ) ) ) $=
      ( wi com24 com45 ) ADCEBFHADCBEFABCDEFHGIJI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate left.  (Contributed by Jeff Hankins,
       28-Jun-2009.)  (The proof was shortened by Wolf Lammen, 29-Jul-2012.) $)
    com5l $p |- ( ps -> ( ch -> ( th -> ( ta -> ( ph -> et ) ) ) ) ) $=
      ( wi com4l com45 ) BCDAEFABCDEFHGIJ $.
      $( [29-Jul-2012] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Swap 1st and 5th.  (Contributed by Jeff
       Hankins, 28-Jun-2009.)  (The proof was shortened by Wolf Lammen,
       29-Jul-2012.) $)
    com15 $p |- ( ta -> ( ps -> ( ch -> ( th -> ( ph -> et ) ) ) ) ) $=
      ( wi com5l com4r ) BCDEAFHABCDEFGIJ $.
      $( [29-Jul-2012] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate left twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52l $p |- ( ch -> ( th -> ( ta -> ( ph -> ( ps -> et ) ) ) ) ) $=
      ( com5l ) BCDEAFABCDEFGHH $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate right twice.  (Contributed by Jeff
       Hankins, 28-Jun-2009.) $)
    com52r $p |- ( th -> ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) ) $=
      ( com52l com5l ) CDEABFABCDEFGHI $.
      $( [18-Apr-2010] $) $( [28-Jun-2009] $)

    $( Commutation of antecedents.  Rotate right.  (Contributed by Wolf Lammen,
       29-Jul-2012.) $)
    com5r $p |- ( ta -> ( ph -> ( ps -> ( ch -> ( th -> et ) ) ) ) ) $=
      ( com52l ) CDEABFABCDEFGHH $.
      $( [29-Jul-2012] $)
  $}

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 9-May-2013.) $)
  jarr $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi ax-1 imim1i ) BABDCBAEF $.
    $( [9-May-2013] $)

  ${
    pm2.86i.1 $e |- ( ( ph -> ps ) -> ( ph -> ch ) ) $.
    $( Inference based on ~ pm2.86 .  (The proof was shortened by Wolf Lammen,
       3-Apr-2013.) $)
    pm2.86i $p |- ( ph -> ( ps -> ch ) ) $=
      ( wi ax-1 syl com12 ) BACBABEACEBAFDGH $.
      $( [3-Apr-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    pm2.86d.1 $e |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $.
    $( Deduction based on ~ pm2.86 .  (The proof was shortened by Wolf Lammen,
       3-Apr-2013.) $)
    pm2.86d $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi ax-1 syl5 com23 ) ACBDCBCFABDFCBGEHI $.
      $( [3-Apr-2013] $) $( [29-Jun-1995] $)
  $}

  $( Converse of axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108.
     (The proof was shortened by Wolf Lammen, 3-Apr-2013.) $)
  pm2.86 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) ->
              ( ph -> ( ps -> ch ) ) ) $=
    ( wi id pm2.86d ) ABDACDDZABCGEF $.
    $( [3-Apr-2013] $) $( [25-Apr-1994] $)

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  This version of ~ loolin does not use ~ ax-3 , meaning
     that this theorem is intuitionistically valid.  (Contributed by O'Cat,
     12-Aug-2004.) $)
  loolinALT $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    ( wi jarr pm2.43d ) ABCBACZCBAABFDE $.
    $( [21-Sep-2013] $) $( [12-Aug-2004] $)

  $( An alternate for the Linearity Axiom of the infinite-valued sentential
     logic (L-infinity) of Lukasiewicz, due to Barbara Wozniakowska, _Reports
     on Mathematical Logic_ 10, 129-137 (1978).  (Contributed by O'Cat,
     8-Aug-2004.) $)
  loowoz $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) ->
                 ( ( ps -> ph ) -> ( ps -> ch ) ) ) $=
    ( wi jarr a2d ) ABDACDZDBACABGEF $.
    $( [20-Sep-2013] $) $( [8-Aug-2004] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical conjunction and logical equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connectives for conjunction ('and') and biconditional. $)
  $c /\ $. $( Wedge (read:  'and') $)
  $c <-> $. $( Double arrow (read:  'if and only if' or
               'is logically equivalent to') $)

  $( Extend wff definition to include conjunction ('and'). $)
  wa $a wff ( ph /\ ps ) $.

  $( Extend our wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.

  $( Left 'and' elimination.  Axiom 1 of 10 for intuitionistic logic. $)
  ax-ia1 $a |- ( ( ph /\ ps ) -> ph ) $.

  $( Right 'and' elimination.  Axiom 2 of 10 for intuitionistic logic. $)
  ax-ia2 $a |- ( ( ph /\ ps ) -> ps ) $.

  $( 'And' introduction.  Axiom 3 of 10 for intuitionistic logic. $)
  ax-ia3 $a |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $.

  $( Elimination of a conjunct.  Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (The proof was shortened by Wolf Lammen, 13-Nov-2012.) $)
  simpl $p |- ( ( ph /\ ps ) -> ph ) $=
    ( ax-ia1 ) ABC $.
    $( [31-Jan-2015] $) $( [5-Aug-1993] $)

  $( Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (The proof was shortened by Wolf Lammen, 13-Nov-2012.) $)
  simpr $p |- ( ( ph /\ ps ) -> ps ) $=
    ( ax-ia2 ) ABC $.
    $( [31-Jan-2015] $) $( [5-Aug-1993] $)

  ${
    simpli.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct. $)
    simpli $p |- ph $=
      ( wa simpl ax-mp ) ABDACABEF $.
      $( [15-Jun-1994] $)
  $}

  ${
    simpld.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    simpld $p |- ( ph -> ps ) $=
      ( wa simpl syl ) ABCEBDBCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    simpri.1 $e |- ( ph /\ ps ) $.
    $( Inference eliminating a conjunct. $)
    simpri $p |- ps $=
      ( wa simpr ax-mp ) ABDBCABEF $.
      $( [15-Jun-1994] $)
  $}

  ${
    simprd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (The proof was shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    simprd $p |- ( ph -> ch ) $=
      ( wa simpr syl ) ABCECDBCFG $.
      $( [3-Oct-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    exp.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per the
       June 2006 Metamath spec change.)  (The proof was shortened by Eric
       Schmidt, 22-Dec-2006.) $)
    ex $p |- ( ph -> ( ps -> ch ) ) $=
      ( wa ax-ia3 syl6 ) ABABECABFDG $.
      $( [31-Jan-2015] $) $( [5-Aug-1993] $)

    $( Exportation inference with commuted antecedents. $)
    expcom $p |- ( ps -> ( ph -> ch ) ) $=
      ( ex com12 ) ABCABCDEF $.
      $( [25-May-2005] $)
  $}

  $( This is our first definition, which introduces and defines the
     biconditional connective ` <-> ` .  We define a wff of the form
     ` ( ph <-> ps ) ` as an abbreviation for
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

     Unlike most traditional developments, we have chosen not to have a
     separate symbol such as "Df." to mean "is defined as."  Instead, we will
     later use the biconditional connective for this purpose ( ~ df-or is its
     first use), as it allows us to use logic to manipulate definitions
     directly.  This greatly simplifies many proofs since it eliminates the
     need for a separate mechanism for introducing and eliminating
     definitions.  Of course, we cannot use this mechanism to define the
     biconditional itself, since it hasn't been introduced yet.  Instead, we
     use a more general form of definition, described as follows.

     In its most general form, a definition is simply an assertion that
     introduces a new symbol (or a new combination of existing symbols, as in
     ~ df-3an ) that is eliminable and does not strengthen the existing
     language.  The latter requirement means that the set of provable
     statements not containing the new symbol (or new combination) should
     remain exactly the same after the definition is introduced.  Our
     definition of the biconditional may look unusual compared to most
     definitions, but it strictly satisfies these requirements.

     The justification for our definition is that if we mechanically replace
     ` ( ph <-> ps ) ` (the definiendum i.e. the thing being defined) with
     ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` (the definiens i.e. the
     defining expression) in the definition, the definition becomes the
     previously proved theorem ~ bijust .  It is impossible to use ~ df-bi to
     prove any statement expressed in the original language that can't be
     proved from the original axioms, because if we simply replace each
     instance of ~ df-bi in the proof with the corresponding ~ bijust instance,
     we will end up with a proof from the original axioms.

     Note that from Metamath's point of view, a definition is just another
     axiom - i.e. an assertion we claim to be true - but from our high level
     point of view, we are are not strengthening the language.  To indicate
     this fact, we prefix definition labels with "df-" instead of "ax-".  (This
     prefixing is an informal convention that means nothing to the Metamath
     proof verifier; it is just for human readability.)

     See ~ dfbi1 , ~ dfbi2 , and ~ dfbi3 for theorems suggesting typical
     textbook definitions of ` <-> ` , showing that our definition has the
     properties we expect.  Theorem ~ dfbi shows this definition rewritten in
     an abbreviated form after conjunction is introduced, for easier
     understanding. $)
  df-bi $a |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
        /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

  $( Property of the biconditional connective. $)
  bi1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wi wa df-bi simpli simpld ) ABCZABDZBADZIJKEZDLIDABFGH $.
    $( [31-Jan-2015] $) $( [11-May-1999] $)

  $( Property of the biconditional connective. $)
  bi3 $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $=
    ( wi wb wa df-bi simpri ex ) ABCZBACZABDZKIJEZCLKCABFGH $.
    $( [11-May-1999] $)

  ${
    biimpi.1 $e |- ( ph <-> ps ) $.
    $( Infer an implication from a logical equivalence. $)
    biimpi $p |- ( ph -> ps ) $=
      ( wb wi bi1 ax-mp ) ABDABECABFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylbi.1 $e |- ( ph <-> ps ) $.
    sylbi.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition. $)
    sylbi $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCABDFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    imp.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation inference.  (The proof was shortened by Eric Schmidt,
       22-Dec-2006.) $)
    imp $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa simpl simpr sylc ) ABEABCABFABGDH $.
      $( [31-Jan-2015] $) $( [5-Aug-1993] $)

    $( Importation inference with commuted antecedents. $)
    impcom $p |- ( ( ps /\ ph ) -> ch ) $=
      ( com12 imp ) BACABCDEF $.
      $( [25-May-2005] $)
  $}

  ${
    impbii.1 $e |- ( ph -> ps ) $.
    impbii.2 $e |- ( ps -> ph ) $.
    $( Infer an equivalence from an implication and its converse. $)
    impbii $p |- ( ph <-> ps ) $=
      ( wi wb bi3 mp2 ) ABEBAEABFCDABGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    impbidd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    impbidd.2 $e |- ( ph -> ( ps -> ( th -> ch ) ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Rodolfo
       Medina, 12-Oct-2010.) $)
    impbidd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi wb bi3 syl6c ) ABCDGDCGCDHEFCDIJ $.
      $( [12-Oct-2010] $)
  $}

  ${
    impbid21d.1 $e |- ( ps -> ( ch -> th ) ) $.
    impbid21d.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduce an equivalence from two implications.  (Contributed by Wolf
       Lammen, 12-May-2013.) $)
    impbid21d $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi a1i a1d impbidd ) ABCDBCDGGAEHADCGBFIJ $.
      $( [12-May-2013] $)
  $}

  ${
    impbid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Deduce an equivalence from two implications.  (Dependency on df-an
       removed by Wolf Lammen, 3-Nov-2012.) $)
    impbid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb impbid21d pm2.43i ) ABCFAABCDEGH $.
      $( [3-Nov-2012] $) $( [5-Aug-1993] $)
  $}

  $( Property of the biconditional connective.  (The proof was shortened by
     Wolf Lammen, 11-Nov-2012.) $)
  bi2 $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    ( wb wi wa df-bi simpli simprd ) ABCZABDZBADZIJKEZDLIDABFGH $.
    $( [31-Jan-2015] $) $( [11-May-1999] $)

  $( Commutative law for equivalence.  (Contributed by Wolf Lammen,
     10-Nov-2012.) $)
  bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    ( wb bi2 bi1 impbid ) ABCBAABDABEF $.
    $( [10-Nov-2012] $)

  ${
    bicomi.1 $e |- ( ph <-> ps ) $.
    $( Inference from commutative law for logical equivalence. $)
    bicomi $p |- ( ps <-> ph ) $=
      ( wb bicom1 ax-mp ) ABDBADCABEF $.
      $( [16-Sep-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    biimpri.1 $e |- ( ph <-> ps ) $.
    $( Infer a converse implication from a logical equivalence.  (The proof was
       shortened by Wolf Lammen, 16-Sep-2013.) $)
    biimpri $p |- ( ps -> ph ) $=
      ( bicomi biimpi ) BAABCDE $.
      $( [16-Sep-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    sylbir.1 $e |- ( ps <-> ph ) $.
    sylbir.2 $e |- ( ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication. $)
    sylbir $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCBADFEG $.
      $( [5-Aug-1993] $)
  $}

  $( Join antecedents with conjunction.  Theorem *3.2 of [WhiteheadRussell]
     p. 111.  (The proof was shortened by Wolf Lammen, 12-Nov-2012.) $)
  pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    ( wa id ex ) ABABCZFDE $.
    $( [12-Nov-2012] $) $( [5-Aug-1993] $)

  ${
    sylib.1 $e |- ( ph -> ps ) $.
    sylib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional. $)
    sylib $p |- ( ph -> ch ) $=
      ( biimpi syl ) ABCDBCEFG $.
      $( [5-Aug-1993] $)
  $}

  $( Commutative law for equivalence.  Theorem *4.21 of [WhiteheadRussell]
     p. 117. $)
  bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $=
    ( wb bicom1 impbii ) ABCBACABDBADE $.
    $( [11-Nov-2012] $) $( [5-Aug-1993] $)

  ${
    bicomd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Commute two sides of a biconditional in a deduction. $)
    bicomd $p |- ( ph -> ( ch <-> ps ) ) $=
      ( wb bicom sylib ) ABCECBEDBCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    impbid1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impbid1.2 $e |- ( ch -> ps ) $.
    $( Infer an equivalence from two implications. $)
    impbid1 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wi a1i impbid ) ABCDCBFAEGH $.
      $( [6-Mar-2007] $)
  $}

  ${
    impbid2.1 $e |- ( ps -> ch ) $.
    impbid2.2 $e |- ( ph -> ( ch -> ps ) ) $.
    $( Infer an equivalence from two implications.  (The proof was shortened by
       Wolf Lammen, 27-Sep-2013.) $)
    impbid2 $p |- ( ph -> ( ps <-> ch ) ) $=
      ( impbid1 bicomd ) ACBACBEDFG $.
      $( [27-Sep-2013] $) $( [6-Mar-2007] $)
  $}

  ${
    biimpd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce an implication from a logical equivalence. $)
    biimpd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb wi bi1 syl ) ABCEBCFDBCGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbi.min $e |- ph $.
    mpbi.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens. $)
    mpbi $p |- ps $=
      ( biimpi ax-mp ) ABCABDEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbir.min $e |- ps $.
    mpbir.maj $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus ponens. $)
    mpbir $p |- ph $=
      ( biimpri ax-mp ) BACABDEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbid.min $e |- ( ph -> ps ) $.
    mpbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens. $)
    mpbid $p |- ( ph -> ch ) $=
      ( biimpd mpd ) ABCDABCEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbii.min $e |- ps $.
    mpbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.  (The
       proof was shortened by Wolf Lammen, 25-Oct-2012.) $)
    mpbii $p |- ( ph -> ch ) $=
      ( a1i mpbid ) ABCBADFEG $.
      $( [25-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    sylibr.1 $e |- ( ph -> ps ) $.
    sylibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting a consequent with a definition. $)
    sylibr $p |- ( ph -> ch ) $=
      ( biimpri syl ) ABCDCBEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylibd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( A syllogism deduction. $)
    sylibd $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syld ) ABCDEACDFGH $.
      $( [3-Aug-1994] $)
  $}

  ${
    sylbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylbid.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction. $)
    sylbid $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syld ) ABCDABCEGFH $.
      $( [3-Aug-1994] $)
  $}

  ${
    mpbidi.min $e |- ( th -> ( ph -> ps ) ) $.
    mpbidi.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens. $)
    mpbidi $p |- ( th -> ( ph -> ch ) ) $=
      ( biimpd sylcom ) DABCEABCFGH $.
      $( [9-Aug-1994] $)
  $}

  ${
    syl5bi.1 $e |- ( ph <-> ps ) $.
    syl5bi.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded antecedent with a
       definition. $)
    syl5bi $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpi syl5 ) ABCDABEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5bir.1 $e |- ( ps <-> ph ) $.
    syl5bir.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional. $)
    syl5bir $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpri syl5 ) ABCDBAEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5ib.1 $e |- ( ph -> ps ) $.
    syl5ib.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference. $)
    syl5ib $p |- ( ch -> ( ph -> th ) ) $=
      ( biimpd syl5 ) ABCDECBDFGH $.
      $( [5-Aug-1993] $)

    $( A mixed syllogism inference. $)
    syl5ibcom $p |- ( ph -> ( ch -> th ) ) $=
      ( syl5ib com12 ) CADABCDEFGH $.
      $( [19-Jun-2007] $)
  $}

  ${
    syl5ibr.1 $e |- ( ph -> th ) $.
    syl5ibr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A mixed syllogism inference. $)
    syl5ibr $p |- ( ch -> ( ph -> ps ) ) $=
      ( bicomd syl5ib ) ADCBECBDFGH $.
      $( [22-Sep-2013] $) $( [3-Apr-1994] $)

    $( A mixed syllogism inference. $)
    syl5ibrcom $p |- ( ph -> ( ch -> ps ) ) $=
      ( syl5ibr com12 ) CABABCDEFGH $.
      $( [20-Jun-2007] $)
  $}

  ${
    biimprd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a converse implication from a logical equivalence.  (The proof
       was shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimprd $p |- ( ph -> ( ch -> ps ) ) $=
      ( id syl5ibr ) CBACCEDF $.
      $( [22-Sep-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    biimpcd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduce a commuted implication from a logical equivalence.  (The proof
       was shortened by Wolf Lammen, 22-Sep-2013.) $)
    biimpcd $p |- ( ps -> ( ph -> ch ) ) $=
      ( id syl5ibcom ) BBACBEDF $.
      $( [22-Sep-2013] $) $( [3-May-1994] $)

    $( Deduce a converse commuted implication from a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 20-Dec-2013.) $)
    biimprcd $p |- ( ch -> ( ph -> ps ) ) $=
      ( id syl5ibrcom ) CBACCEDF $.
      $( [20-Dec-2013] $) $( [3-May-1994] $)
  $}

  ${
    syl6ib.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ib.2 $e |- ( ch <-> th ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional. $)
    syl6ib $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpi syl6 ) ABCDECDFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6ibr.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl6ibr.2 $e |- ( th <-> ch ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition. $)
    syl6ibr $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpri syl6 ) ABCDEDCFGH $.
      $( [5-Aug-1993] $)
  $}


  ${
    syl6bi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bi.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference. $)
    syl6bi $p |- ( ph -> ( ps -> th ) ) $=
      ( biimpd syl6 ) ABCDABCEGFH $.
      $( [2-Jan-1994] $)
  $}

  ${
    syl6bir.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    syl6bir.2 $e |- ( ch -> th ) $.
    $( A mixed syllogism inference. $)
    syl6bir $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syl6 ) ABCDACBEGFH $.
      $( [18-May-1994] $)
  $}

  ${
    syl7bi.1 $e |- ( ph <-> ps ) $.
    syl7bi.2 $e |- ( ch -> ( th -> ( ps -> ta ) ) ) $.
    $( A mixed syllogism inference from a doubly nested implication and a
       biconditional. $)
    syl7bi $p |- ( ch -> ( th -> ( ph -> ta ) ) ) $=
      ( biimpi syl7 ) ABCDEABFHGI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl8ib.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    syl8ib.2 $e |- ( th <-> ta ) $.
    $( A syllogism rule of inference.  The second premise is used to replace
       the consequent of the first premise. $)
    syl8ib $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( biimpi syl8 ) ABCDEFDEGHI $.
      $( [1-Aug-1994] $)
  $}

  ${
    mpbird.min $e |- ( ph -> ch ) $.
    mpbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens. $)
    mpbird $p |- ( ph -> ps ) $=
      ( biimprd mpd ) ACBDABCEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    mpbiri.min $e |- ch $.
    mpbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a nested biconditional, related to modus ponens.  (The
       proof was shortened by Wolf Lammen, 25-Oct-2012.) $)
    mpbiri $p |- ( ph -> ps ) $=
      ( a1i mpbird ) ABCCADFEG $.
      $( [25-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    sylibrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibrd.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism deduction. $)
    sylibrd $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syld ) ABCDEADCFGH $.
      $( [3-Aug-1994] $)
  $}

  ${
    sylbird.1 $e |- ( ph -> ( ch <-> ps ) ) $.
    sylbird.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( A syllogism deduction. $)
    sylbird $p |- ( ph -> ( ps -> th ) ) $=
      ( biimprd syld ) ABCDACBEGFH $.
      $( [3-Aug-1994] $)
  $}

  $( Principle of identity for logical equivalence.  Theorem *4.2 of
     [WhiteheadRussell] p. 117. $)
  biid $p |- ( ph <-> ph ) $=
    ( id impbii ) AAABZDC $.
    $( [5-Aug-1993] $)

  $( Principle of identity with antecedent. $)
  biidd $p |- ( ph -> ( ps <-> ps ) ) $=
    ( wb biid a1i ) BBCABDE $.
    $( [25-Nov-1995] $)

  $( Two propositions are equivalent if they are both true.  Closed form of
     ~ 2th .  Equivalent to a ~ bi1 -like version of the xor-connective.  This
     theorem stays true, no matter how you permute its operands.  This is
     evident from its sharper version
     ` ( ph <-> ( ps <-> ( ph <-> ps ) ) ) ` .  (Contributed by Wolf Lammen,
     12-May-2013.) $)
  pm5.1im $p |- ( ph -> ( ps -> ( ph <-> ps ) ) ) $=
    ( ax-1 impbid21d ) ABABBACABCD $.
    $( [12-May-2013] $)

  ${
    2th.1 $e |- ph $.
    2th.2 $e |- ps $.
    $( Two truths are equivalent. $)
    2th $p |- ( ph <-> ps ) $=
      ( a1i impbii ) ABBADEABCEF $.
      $( [18-Aug-1993] $)
  $}

  ${
    2thd.1 $e |- ( ph -> ps ) $.
    2thd.2 $e |- ( ph -> ch ) $.
    $( Two truths are equivalent (deduction rule). $)
    2thd $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb pm5.1im sylc ) ABCBCFDEBCGH $.
      $( [29-Jan-2013] $) $( [3-Jun-2012] $)
  $}

  ${
    ibi.1 $e |- ( ph -> ( ph <-> ps ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication. $)
    ibi $p |- ( ph -> ps ) $=
      ( biimpd pm2.43i ) ABAABCDE $.
      $( [17-Oct-2003] $)
  $}

  ${
    ibir.1 $e |- ( ph -> ( ps <-> ph ) ) $.
    $( Inference that converts a biconditional implied by one of its arguments,
       into an implication. $)
    ibir $p |- ( ph -> ps ) $=
      ( bicomd ibi ) ABABACDE $.
      $( [22-Jul-2004] $)
  $}

  ${
    ibd.1 $e |- ( ph -> ( ps -> ( ps <-> ch ) ) ) $.
    $( Deduction that converts a biconditional implied by one of its arguments,
       into an implication. $)
    ibd $p |- ( ph -> ( ps -> ch ) ) $=
      ( wb bi1 syli ) BABCECDBCFG $.
      $( [26-Jun-2004] $)
  $}

  $( Distribution of implication over biconditional.  Theorem *5.74 of
     [WhiteheadRussell] p. 126.  (The proof was shortened by Wolf Lammen,
     11-Apr-2013.) $)
  pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $=
    ( wb wi bi1 imim3i bi2 impbid pm2.86d impbidd impbii ) ABCDZEZABEZACEZDZNOP
    MBCABCFGMCBABCHGIQABCQABCOPFJQACBOPHJKL $.
    $( [11-Apr-2013] $) $( [1-Aug-1994] $)

  ${
    pm5.74i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule). $)
    pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $=
      ( wb wi pm5.74 mpbi ) ABCEFABFACFEDABCGH $.
      $( [1-Aug-1994] $)
  $}

  ${
    pm5.74ri.1 $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
    $( Distribution of implication over biconditional (reverse inference
       rule). $)
    pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wb wi pm5.74 mpbir ) ABCEFABFACFEDABCGH $.
      $( [1-Aug-1994] $)
  $}

  ${
    pm5.74d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.74d $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb wi pm5.74 sylib ) ABCDFGBCGBDGFEBCDHI $.
      $( [21-Mar-1996] $)
  $}

  ${
    pm5.74rd.1 $e |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.74rd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $=
      ( wi wb pm5.74 sylibr ) ABCFBDFGBCDGFEBCDHI $.
      $( [19-Mar-1997] $)
  $}

  ${
    bitri.1 $e |- ( ph <-> ps ) $.
    bitri.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (The proof
       was shortened by Wolf Lammen, 13-Oct-2012.) $)
    bitri $p |- ( ph <-> ch ) $=
      ( biimpi sylib biimpri sylibr impbii ) ACABCABDFEGCBABCEHDIJ $.
      $( [13-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    bitr2i.1 $e |- ( ph <-> ps ) $.
    bitr2i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitr2i $p |- ( ch <-> ph ) $=
      ( bitri bicomi ) ACABCDEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr3i.1 $e |- ( ps <-> ph ) $.
    bitr3i.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitr3i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCBADFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr4i.1 $e |- ( ph <-> ps ) $.
    bitr4i.2 $e |- ( ch <-> ps ) $.
    $( An inference from transitive law for logical equivalence. $)
    bitr4i $p |- ( ph <-> ch ) $=
      ( bicomi bitri ) ABCDCBEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitri .  (The proof was shortened by Wolf Lammen,
       14-Apr-2013.) $)
    bitrd $p |- ( ph -> ( ps <-> th ) ) $=
      ( wi pm5.74i bitri pm5.74ri ) ABDABGACGADGABCEHACDFHIJ $.
      $( [14-Apr-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr2d.2 $e |- ( ph -> ( ch <-> th ) ) $.
    $( Deduction form of ~ bitr2i . $)
    bitr2d $p |- ( ph -> ( th <-> ps ) ) $=
      ( bitrd bicomd ) ABDABCDEFGH $.
      $( [9-Jun-2004] $)
  $}

  ${
    bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    $( Deduction form of ~ bitr3i . $)
    bitr3d $p |- ( ph -> ( ch <-> th ) ) $=
      ( bicomd bitrd ) ACBDABCEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr4d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( Deduction form of ~ bitr4i . $)
    bitr4d $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomd bitrd ) ABCDEADCFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5bb.1 $e |- ( ph <-> ps ) $.
    syl5bb.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5bb $p |- ( ch -> ( ph <-> th ) ) $=
      ( wb a1i bitrd ) CABDABGCEHFI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5rbb.1 $e |- ( ph <-> ps ) $.
    syl5rbb.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5rbb $p |- ( ch -> ( th <-> ph ) ) $=
      ( syl5bb bicomd ) CADABCDEFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5bbr.1 $e |- ( ps <-> ph ) $.
    syl5bbr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5bbr $p |- ( ch -> ( ph <-> th ) ) $=
      ( bicomi syl5bb ) ABCDBAEGFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl5rbbr.1 $e |- ( ps <-> ph ) $.
    syl5rbbr.2 $e |- ( ch -> ( ps <-> th ) ) $.
    $( A syllogism inference from two biconditionals. $)
    syl5rbbr $p |- ( ch -> ( th <-> ph ) ) $=
      ( bicomi syl5rbb ) ABCDBAEGFH $.
      $( [25-Nov-1994] $)
  $}

  ${
    syl6bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6bb $p |- ( ph -> ( ps <-> th ) ) $=
      ( wb a1i bitrd ) ABCDECDGAFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6rbb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbb.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6rbb $p |- ( ph -> ( th <-> ps ) ) $=
      ( syl6bb bicomd ) ABDABCDEFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6bbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6bbr $p |- ( ph -> ( ps <-> th ) ) $=
      ( bicomi syl6bb ) ABCDEDCFGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl6rbbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl6rbbr.2 $e |- ( th <-> ch ) $.
    $( A syllogism inference from two biconditionals. $)
    syl6rbbr $p |- ( ph -> ( th <-> ps ) ) $=
      ( bicomi syl6rbb ) ABCDEDCFGH $.
      $( [25-Nov-1994] $)
  $}

  ${
    3imtr3.1 $e |- ( ph -> ps ) $.
    3imtr3.2 $e |- ( ph <-> ch ) $.
    3imtr3.3 $e |- ( ps <-> th ) $.
    $( A mixed syllogism inference, useful for removing a definition from both
       sides of an implication. $)
    3imtr3i $p |- ( ch -> th ) $=
      ( sylbir sylib ) CBDCABFEHGI $.
      $( [10-Aug-1994] $)
  $}

  ${
    3imtr4.1 $e |- ( ph -> ps ) $.
    3imtr4.2 $e |- ( ch <-> ph ) $.
    3imtr4.3 $e |- ( th <-> ps ) $.
    $( A mixed syllogism inference, useful for applying a definition to both
       sides of an implication. $)
    3imtr4i $p |- ( ch -> th ) $=
      ( sylbi sylibr ) CBDCABFEHGI $.
      $( [5-Aug-1993] $)
  $}

  ${
    3imtr3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3imtr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting conditional
       definitions in a formula. $)
    3imtr3d $p |- ( ph -> ( th -> ta ) ) $=
      ( sylibd sylbird ) ADBEGABCEFHIJ $.
      $( [8-Apr-1996] $)
  $}

  ${
    3imtr4d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3imtr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting conditional
       definitions in a formula. $)
    3imtr4d $p |- ( ph -> ( th -> ta ) ) $=
      ( sylibrd sylbid ) ADBEGABCEFHIJ $.
      $( [26-Oct-1995] $)
  $}

  ${
    3imtr3g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr3g.2 $e |- ( ps <-> th ) $.
    3imtr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3imtr3i .  Useful for converting definitions
       in a formula.  (The proof was shortened by Wolf Lammen, 20-Dec-2013.) $)
    3imtr3g $p |- ( ph -> ( th -> ta ) ) $=
      ( syl5bir syl6ib ) ADCEDBACGFIHJ $.
      $( [20-Dec-2013] $) $( [20-May-1996] $)
  $}

  ${
    3imtr4g.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3imtr4g.2 $e |- ( th <-> ps ) $.
    3imtr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3imtr4i .  Useful for converting definitions
       in a formula.  (The proof was shortened by Wolf Lammen, 20-Dec-2013.) $)
    3imtr4g $p |- ( ph -> ( th -> ta ) ) $=
      ( syl5bi syl6ibr ) ADCEDBACGFIHJ $.
      $( [20-Dec-2013] $) $( [20-May-1996] $)
  $}

  ${
    3bitri.1 $e |- ( ph <-> ps ) $.
    3bitri.2 $e |- ( ps <-> ch ) $.
    3bitri.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence. $)
    3bitri $p |- ( ph <-> th ) $=
      ( bitri ) ABDEBCDFGHH $.
      $( [5-Aug-1993] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitrri $p |- ( th <-> ph ) $=
      ( bitr2i bitr3i ) DCAGABCEFHI $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr2i.1 $e |- ( ph <-> ps ) $.
    3bitr2i.2 $e |- ( ch <-> ps ) $.
    3bitr2i.3 $e |- ( ch <-> th ) $.
    $( A chained inference from transitive law for logical equivalence. $)
    3bitr2i $p |- ( ph <-> th ) $=
      ( bitr4i bitri ) ACDABCEFHGI $.
      $( [4-Aug-2006] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitr2ri $p |- ( th <-> ph ) $=
      ( bitr4i bitr2i ) ACDABCEFHGI $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr3i.1 $e |- ( ph <-> ps ) $.
    3bitr3i.2 $e |- ( ph <-> ch ) $.
    3bitr3i.3 $e |- ( ps <-> th ) $.
    $( A chained inference from transitive law for logical equivalence. $)
    3bitr3i $p |- ( ch <-> th ) $=
      ( bitr3i bitri ) CBDCABFEHGI $.
      $( [19-Aug-1993] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitr3ri $p |- ( th <-> ch ) $=
      ( bitr3i ) DBCGBACEFHH $.
      $( [5-Aug-1993] $)
  $}

  ${
    3bitr4i.1 $e |- ( ph <-> ps ) $.
    3bitr4i.2 $e |- ( ch <-> ph ) $.
    3bitr4i.3 $e |- ( th <-> ps ) $.
    $( A chained inference from transitive law for logical equivalence.  This
       inference is frequently used to apply a definition to both sides of a
       logical equivalence. $)
    3bitr4i $p |- ( ch <-> th ) $=
      ( bitr4i bitri ) CADFABDEGHI $.
      $( [5-Aug-1993] $)

    $( A chained inference from transitive law for logical equivalence. $)
    3bitr4ri $p |- ( th <-> ch ) $=
      ( bitr4i bitr2i ) CADFABDEGHI $.
      $( [2-Sep-1995] $)
  $}

  ${
    3bitrd.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitrd.2 $e |- ( ph -> ( ch <-> th ) ) $.
    3bitrd.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional. $)
    3bitrd $p |- ( ph -> ( ps <-> ta ) ) $=
      ( bitrd ) ABDEABCDFGIHI $.
      $( [13-Aug-1999] $)

    $( Deduction from transitivity of biconditional. $)
    3bitrrd $p |- ( ph -> ( ta <-> ps ) ) $=
      ( bitr2d bitr3d ) ADEBHABCDFGIJ $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr2d.2 $e |- ( ph -> ( th <-> ch ) ) $.
    3bitr2d.3 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction from transitivity of biconditional. $)
    3bitr2d $p |- ( ph -> ( ps <-> ta ) ) $=
      ( bitr4d bitrd ) ABDEABCDFGIHJ $.
      $( [4-Aug-2006] $)

    $( Deduction from transitivity of biconditional. $)
    3bitr2rd $p |- ( ph -> ( ta <-> ps ) ) $=
      ( bitr4d bitr2d ) ABDEABCDFGIHJ $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    3bitr3d.3 $e |- ( ph -> ( ch <-> ta ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula. $)
    3bitr3d $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr3d bitrd ) ADCEABDCGFIHJ $.
      $( [24-Apr-1996] $)

    $( Deduction from transitivity of biconditional. $)
    3bitr3rd $p |- ( ph -> ( ta <-> th ) ) $=
      ( bitr3d ) ACEDHABCDFGII $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr4d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4d.2 $e |- ( ph -> ( th <-> ps ) ) $.
    3bitr4d.3 $e |- ( ph -> ( ta <-> ch ) ) $.
    $( Deduction from transitivity of biconditional.  Useful for converting
       conditional definitions in a formula. $)
    3bitr4d $p |- ( ph -> ( th <-> ta ) ) $=
      ( bitr4d bitrd ) ADBEGABCEFHIJ $.
      $( [18-Oct-1995] $)

    $( Deduction from transitivity of biconditional. $)
    3bitr4rd $p |- ( ph -> ( ta <-> th ) ) $=
      ( bitr4d ) AEBDAECBHFIGI $.
      $( [4-Aug-2006] $)
  $}

  ${
    3bitr3g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr3g.2 $e |- ( ps <-> th ) $.
    3bitr3g.3 $e |- ( ch <-> ta ) $.
    $( More general version of ~ 3bitr3i .  Useful for converting definitions
       in a formula. $)
    3bitr3g $p |- ( ph -> ( th <-> ta ) ) $=
      ( syl5bbr syl6bb ) ADCEDBACGFIHJ $.
      $( [4-Jun-1995] $)
  $}

  ${
    3bitr4g.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3bitr4g.2 $e |- ( th <-> ps ) $.
    3bitr4g.3 $e |- ( ta <-> ch ) $.
    $( More general version of ~ 3bitr4i .  Useful for converting definitions
       in a formula. $)
    3bitr4g $p |- ( ph -> ( th <-> ta ) ) $=
      ( syl5bb syl6bbr ) ADCEDBACGFIHJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    bi3ant.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Construct a bi-conditional in antecedent position.  (Contributed by Wolf
       Lammen, 14-May-2013.) $)
    bi3ant $p |- ( ( ( th -> ta ) -> ph ) -> ( ( ( ta -> th ) -> ps ) ->
                                                ( ( th <-> ta ) -> ch ) ) ) $=
      ( wi wb bi1 imim1i bi2 imim3i syl2im ) DEGZAGDEHZAGEDGZBGOBGOCGONADEIJOPB
      DEKJABCOFLM $.
      $( [14-May-2013] $)
  $}

  $( Express symmetries of theorems in terms of biconditionals.  (Contributed
     by Wolf Lammen, 14-May-2013.) $)
  bisym $p |- ( ( ( ph -> ps ) -> ( ch -> th ) ) -> ( ( ( ps -> ph )
      -> ( th -> ch ) ) -> ( ( ph <-> ps ) -> ( ch <-> th ) ) ) ) $=
    ( wi wb bi3 bi3ant ) CDEDCECDFABCDGH $.
    $( [14-May-2013] $)

  $( The next three rules are useful for building up wff's around a
     definition, in order to make use of the definition. $)

  ${
    bi.a $e |- ( ph <-> ps ) $.
    $( Introduce an antecedent to both sides of a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 6-Feb-2013.) $)
    imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $=
      ( wb a1i pm5.74i ) CABABECDFG $.
      $( [6-Feb-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    bibi.a $e |- ( ph <-> ps ) $.
    $( Inference adding a biconditional to the left in an equivalence.  (The
       proof was shortened by Andrew Salmon, 7-May-2011.)  (The proof was
       shortened by Wolf Lammen, 16-May-2013.) $)
    bibi2i $p |- ( ( ch <-> ph ) <-> ( ch <-> ps ) ) $=
      ( wb id syl6bb syl6bbr impbii ) CAEZCBEZJCABJFDGKCBAKFDHI $.
      $( [16-May-2013] $) $( [5-Aug-1993] $)

    $( Inference adding a biconditional to the right in an equivalence. $)
    bibi1i $p |- ( ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb bicom bibi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
      $( [5-Aug-1993] $)

    ${
      bibi12.2 $e |- ( ch <-> th ) $.
      $( The equivalence of two equivalences. $)
      bibi12i $p |- ( ( ph <-> ch ) <-> ( ps <-> th ) ) $=
        ( wb bibi2i bibi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
        $( [5-Aug-1993] $)
    $}
  $}

  ${
    imbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding an antecedent to both sides of a logical
       equivalence. $)
    imbi2d $p |- ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) ) $=
      ( wb a1d pm5.74d ) ADBCABCFDEGH $.
      $( [5-Aug-1993] $)

    $( Deduction adding a consequent to both sides of a logical equivalence.
       (The proof was shortened by Wolf Lammen, 17-Sep-2013.) $)
    imbi1d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $=
      ( wi biimprd imim1d biimpd impbid ) ABDFCDFACBDABCEGHABCDABCEIHJ $.
      $( [17-Sep-2013] $) $( [5-Aug-1993] $)

    $( Deduction adding a biconditional to the left in an equivalence.  (The
       proof was shortened by Wolf Lammen, 19-May-2013.) $)
    bibi2d $p |- ( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) ) $=
      ( wb wi pm5.74i bibi2i pm5.74 3bitr4i pm5.74ri ) ADBFZDCFZADGZABGZFOACGZF
      AMGANGPQOABCEHIADBJADCJKL $.
      $( [19-May-2013] $) $( [5-Aug-1993] $)

    $( Deduction adding a biconditional to the right in an equivalence. $)
    bibi1d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> th ) ) ) $=
      ( wb bibi2d bicom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    imbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    imbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of
       implications. $)
    imbi12d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $=
      ( wi imbi1d imbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)
    $( Deduction joining two equivalences to form equivalence of
       biconditionals. $)
    bibi12d $p |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) ) $=
      ( wb bibi1d bibi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *4.84 of [WhiteheadRussell] p. 122. $)
  imbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $=
    ( wb id imbi1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  $( Theorem *4.85 of [WhiteheadRussell] p. 122.  (The proof was shortened by
     Wolf Lammen, 19-May-2013.) $)
  imbi2 $p |- ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ) $=
    ( wb id imbi2d ) ABDZABCGEF $.
    $( [19-May-2013] $) $( [3-Jan-2005] $)

  ${
    imbi1i.1 $e |- ( ph <-> ps ) $.
    $( Introduce a consequent to both sides of a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 17-Sep-2013.) $)
    imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $=
      ( wb wi imbi1 ax-mp ) ABEACFBCFEDABCGH $.
      $( [17-Sep-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    imbi12i.1 $e |- ( ph <-> ps ) $.
    imbi12i.2 $e |- ( ch <-> th ) $.
    $( Join two logical equivalences to form equivalence of implications. $)
    imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $=
      ( wi imbi2i imbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *4.86 of [WhiteheadRussell] p. 122. $)
  bibi1 $p |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) <-> ( ps <-> ch ) ) ) $=
    ( wb id bibi1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  $( A wff is equivalent to itself with true antecedent. $)
  biimt $p |- ( ph -> ( ps <-> ( ph -> ps ) ) ) $=
    ( wi ax-1 pm2.27 impbid2 ) ABABCBADABEF $.
    $( [28-Jan-1996] $)

  $( Theorem *5.5 of [WhiteheadRussell] p. 125. $)
  pm5.5 $p |- ( ph -> ( ( ph -> ps ) <-> ps ) ) $=
    ( wi biimt bicomd ) ABABCABDE $.
    $( [3-Jan-2005] $)

  ${
    a1bi.1 $e |- ph $.
    $( Inference rule introducing a theorem as an antecedent.  The proof was
       shortened by Wolf Lammen, 11-Nov-2012.) $)
    a1bi $p |- ( ps <-> ( ph -> ps ) ) $=
      ( wi wb biimt ax-mp ) ABABDECABFG $.
      $( [11-Nov-2012] $) $( [5-Aug-1993] $)
  $}

  $( Theorem *5.501 of [WhiteheadRussell] p. 125. $)
  pm5.501 $p |- ( ph -> ( ps <-> ( ph <-> ps ) ) ) $=
    ( wb pm5.1im bi1 com12 impbid ) ABABCZABDHABABEFG $.
    $( [24-Jan-2013] $) $( [3-Jan-2005] $)

  $( Implication in terms of implication and biconditional.  (The proof was
     shortened by Wolf Lammen, 24-Jan-2013.) $)
  ibib $p |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ) $=
    ( wb pm5.501 pm5.74i ) ABABCABDE $.
    $( [24-Jan-2013] $) $( [31-Mar-1994] $)

  $( Implication in terms of implication and biconditional.  (The proof was
     shortened by Wolf Lammen, 21-Dec-2013.) $)
  ibibr $p |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ) $=
    ( wb pm5.501 bicom syl6bb pm5.74i ) ABBACZABABCHABDABEFG $.
    $( [21-Dec-2013] $) $( [29-Apr-2005] $)

  ${
    tbt.1 $e |- ph $.
    $( A wff is equivalent to its equivalence with truth.  (The proof was
       shortened by Andrew Salmon, 13-May-2011.) $)
    tbt $p |- ( ps <-> ( ps <-> ph ) ) $=
      ( wb ibibr pm5.74ri ax-mp ) ABBADZDCABHABEFG $.
      $( [16-May-2011] $) $( [18-Aug-1993] $)
  $}

  $( Logical equivalence of commuted antecedents.  Part of Theorem *4.87 of
     [WhiteheadRussell] p. 122. $)
  bi2.04 $p |- ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) $=
    ( wi pm2.04 impbii ) ABCDDBACDDABCEBACEF $.
    $( [5-Aug-1993] $)

  $( Antecedent absorption implication.  Theorem *5.4 of [WhiteheadRussell]
     p. 125. $)
  pm5.4 $p |- ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) ) $=
    ( wi pm2.43 ax-1 impbii ) AABCZCGABDGAEF $.
    $( [5-Aug-1993] $)

  $( Distributive law for implication.  Compare Theorem *5.41 of
     [WhiteheadRussell] p. 125. $)
  imdi $p |- ( ( ph -> ( ps -> ch ) ) <->
               ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi ax-2 pm2.86 impbii ) ABCDDABDACDDABCEABCFG $.
    $( [5-Aug-1993] $)

  $( Theorem *5.41 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 12-Oct-2012.) $)
  pm5.41 $p |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) <->
                ( ph -> ( ps -> ch ) ) ) $=
    ( wi imdi bicomi ) ABCDDABDACDDABCEF $.
    $( [13-Oct-2012] $) $( [3-Jan-2005] $)

  $( Simplify an implication between two implications when the antecedent of
     the first is a consequence of the antecedent of the second.  The reverse
     form is useful in producing the successor step in induction proofs.
     (Contributed by Paul Chapman, 22-Jun-2011.)  (The proof was shortened by
     Wolf Lammen, 14-Sep-2013.) $)
  imim21b $p |- ( ( ps -> ph ) -> ( ( ( ph -> ch ) -> ( ps -> th ) ) <->
                                    ( ps -> ( ch -> th ) ) ) ) $=
    ( wi bi2.04 wb pm5.5 imbi1d imim2i pm5.74d syl5bb ) ACEZBDEEBMDEZEBAEZBCDEZ
    EMBDFOBNPANPGBAMCDACHIJKL $.
    $( [14-Sep-2013] $) $( [22-Jun-2011] $)

  ${
    imp3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation deduction. $)
    imp3a $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( wa wi com3l imp com12 ) BCFADBCADGABCDEHIJ $.
      $( [24-Mar-2013] $) $( [31-Mar-1994] $)

    $( An importation inference. $)
    imp31 $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( wa wi imp ) ABFCDABCDGEHH $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp32 $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( wa imp3a imp ) ABCFDABCDEGH $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp3a.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Exportation deduction. $)
    exp3a $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi wa com12 ex com3r ) BCADBCADFABCGDEHIJ $.
      $( [24-Mar-2013] $) $( [20-Aug-1993] $)

    $( A deduction version of exportation, followed by importation. $)
    expdimp $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi exp3a imp ) ABCDFABCDEGH $.
      $( [6-Sep-2008] $)
  $}

  ${
    impancom.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Mixed importation/commutation inference. $)
    impancom $p |- ( ( ph /\ ch ) -> ( ps -> th ) ) $=
      ( wi ex com23 imp ) ACBDFABCDABCDFEGHI $.
      $( [22-Jun-2013] $)
  $}

  $( Theorem *3.3 (Exp) of [WhiteheadRussell] p. 112.  (The proof was shortened
     by Wolf Lammen, 24-Mar-2013.) $)
  pm3.3 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi id exp3a ) ABDCEZABCHFG $.
    $( [24-Mar-2013] $) $( [3-Jan-2005] $)

  $( Theorem *3.31 (Imp) of [WhiteheadRussell] p. 112.  (The proof was
     shortened by Wolf Lammen, 24-Mar-2013.) $)
  pm3.31 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wi id imp3a ) ABCDDZABCGEF $.
    $( [24-Mar-2013] $) $( [3-Jan-2005] $)

  $( Import-export theorem.  Part of Theorem *4.87 of [WhiteheadRussell]
     p. 122.  (The proof was shortened by Wolf Lammen, 24-Mar-2013.) $)
  impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi pm3.3 pm3.31 impbii ) ABDCEABCEEABCFABCGH $.
    $( [24-Mar-2013] $) $( [5-Aug-1993] $)

  $( Join antecedents with conjunction.  Theorem *3.21 of [WhiteheadRussell]
     p. 111. $)
  pm3.21 $p |- ( ph -> ( ps -> ( ps /\ ph ) ) ) $=
    ( wa pm3.2 com12 ) BABACBADE $.
    $( [5-Aug-1993] $)

  $( Theorem *3.22 of [WhiteheadRussell] p. 111.  (The proof was shortened by
     Wolf Lammen, 13-Nov-2012.) $)
  pm3.22 $p |- ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
    ( wa pm3.21 imp ) ABBACABDE $.
    $( [13-Nov-2012] $) $( [3-Jan-2005] $)

  $( Commutative law for conjunction.  Theorem *4.3 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Wolf Lammen, 4-Nov-2012.) $)
  ancom $p |- ( ( ph /\ ps ) <-> ( ps /\ ph ) ) $=
    ( wa pm3.22 impbii ) ABCBACABDBADE $.
    $( [4-Nov-2012] $) $( [25-Jun-1998] $)

  ${
    ancomd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Commutation of conjuncts in consequent.  (Contributed by Jeff Hankins,
       14-Aug-2009.) $)
    ancomd $p |- ( ph -> ( ch /\ ps ) ) $=
      ( wa ancom sylib ) ABCECBEDBCFG $.
      $( [18-Apr-2010] $) $( [14-Aug-2009] $)
  $}

  ${
    ancoms.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference commuting conjunction in antecedent. $)
    ancoms $p |- ( ( ps /\ ph ) -> ch ) $=
      ( expcom imp ) BACABCDEF $.
      $( [21-Apr-1994] $)
  $}

  ${
    ancomsd.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction commuting conjunction in antecedent. $)
    ancomsd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $=
      ( wa ancom syl5bi ) CBFBCFADCBGEH $.
      $( [12-Dec-2004] $)
  $}

  ${
    pm3.2i.1 $e |- ph $.
    pm3.2i.2 $e |- ps $.
    $( Infer conjunction of premises. $)
    pm3.2i $p |- ( ph /\ ps ) $=
      ( wa pm3.2 mp2 ) ABABECDABFG $.
      $( [5-Aug-1993] $)
  $}

  $( Nested conjunction of antecedents. $)
  pm3.43i $p |- ( ( ph -> ps ) ->
                ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ) $=
    ( wa pm3.2 imim3i ) BCBCDABCEF $.
    $( [5-Aug-1993] $)

  ${
    simplbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    simplbi $p |- ( ph -> ps ) $=
      ( wa biimpi simpld ) ABCABCEDFG $.
      $( [27-May-1998] $)
  $}

  ${
    simprbi.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct. $)
    simprbi $p |- ( ph -> ch ) $=
      ( wa biimpi simprd ) ABCABCEDFG $.
      $( [27-May-1998] $)
  $}

  ${
    adantr.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the right of an antecedent. $)
    adantr $p |- ( ( ph /\ ch ) -> ps ) $=
      ( a1d imp ) ACBABCDEF $.
      $( [30-Aug-1993] $)
  $}

  ${
    adantl.1 $e |- ( ph -> ps ) $.
    $( Inference adding a conjunct to the left of an antecedent.  (The proof
       was shortened by Wolf Lammen, 23-Nov-2012.) $)
    adantl $p |- ( ( ch /\ ph ) -> ps ) $=
      ( adantr ancoms ) ACBABCDEF $.
      $( [23-Nov-2012] $) $( [30-Aug-1993] $)
  $}

  ${
    adantld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the left of an antecedent.  (The proof
       was shortened by Wolf Lammen, 20-Dec-2012.) $)
    adantld $p |- ( ph -> ( ( th /\ ps ) -> ch ) ) $=
      ( wa simpr syl5 ) DBFBACDBGEH $.
      $( [20-Dec-2012] $) $( [4-May-1994] $)
  $}

  ${
    adantrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction adding a conjunct to the right of an antecedent. $)
    adantrd $p |- ( ph -> ( ( ps /\ th ) -> ch ) ) $=
      ( wa simpl syl5 ) BDFBACBDGEH $.
      $( [4-May-1994] $)
  $}

  ${
    mpan9.1 $e |- ( ph -> ps ) $.
    mpan9.2 $e |- ( ch -> ( ps -> th ) ) $.
    $( Modus ponens conjoining dissimilar antecedents.  (The proof was
       shortened by Andrew Salmon, 7-May-2011.) $)
    mpan9 $p |- ( ( ph /\ ch ) -> th ) $=
      ( syl5 impcom ) CADABCDEFGH $.
      $( [12-May-2011] $) $( [1-Feb-2008] $)
  $}

  ${
    syldan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    syldan.2 $e |- ( ( ph /\ ch ) -> th ) $.
    $( A syllogism deduction with conjoined antecents.  (The proof was
       shortened by Wolf Lammen, 6-Apr-2013.) $)
    syldan $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa expcom adantrd mpcom ) CABGDECADBACDFHIJ $.
      $( [6-Apr-2013] $) $( [24-Feb-2005] $)
  $}

  ${
    sylan.1 $e |- ( ph -> ps ) $.
    sylan.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (The proof was shortened by Wolf Lammen,
       22-Nov-2012.) $)
    sylan $p |- ( ( ph /\ ch ) -> th ) $=
      ( expcom mpan9 ) ABCDEBCDFGH $.
      $( [22-Nov-2012] $) $( [21-Apr-1994] $)
  $}

  ${
    sylanb.1 $e |- ( ph <-> ps ) $.
    sylanb.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference. $)
    sylanb $p |- ( ( ph /\ ch ) -> th ) $=
      ( biimpi sylan ) ABCDABEGFH $.
      $( [18-May-1994] $)
  $}

  ${
    sylanbr.1 $e |- ( ps <-> ph ) $.
    sylanbr.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference. $)
    sylanbr $p |- ( ( ph /\ ch ) -> th ) $=
      ( biimpri sylan ) ABCDBAEGFH $.
      $( [18-May-1994] $)
  $}

  ${
    sylan2.1 $e |- ( ph -> ch ) $.
    sylan2.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference.  (The proof was shortened by Wolf Lammen,
       22-Nov-2012.) $)
    sylan2 $p |- ( ( ps /\ ph ) -> th ) $=
      ( adantl syldan ) BACDACBEGFH $.
      $( [22-Nov-2012] $) $( [21-Apr-1994] $)
  $}

  ${
    sylan2b.1 $e |- ( ph <-> ch ) $.
    sylan2b.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference. $)
    sylan2b $p |- ( ( ps /\ ph ) -> th ) $=
      ( biimpi sylan2 ) ABCDACEGFH $.
      $( [21-Apr-1994] $)
  $}

  ${
    sylan2br.1 $e |- ( ch <-> ph ) $.
    sylan2br.2 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference. $)
    sylan2br $p |- ( ( ps /\ ph ) -> th ) $=
      ( biimpri sylan2 ) ABCDCAEGFH $.
      $( [21-Apr-1994] $)
  $}

  ${
    syl2an.1 $e |- ( ph -> ps ) $.
    syl2an.2 $e |- ( ta -> ch ) $.
    syl2an.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference. $)
    syl2an $p |- ( ( ph /\ ta ) -> th ) $=
      ( sylan sylan2 ) EACDGABCDFHIJ $.
      $( [31-Jan-1997] $)

    $( A double syllogism inference. $)
    syl2anr $p |- ( ( ta /\ ph ) -> th ) $=
      ( syl2an ancoms ) AEDABCDEFGHIJ $.
      $( [17-Sep-2013] $)
  $}

  ${
    syl2anb.1 $e |- ( ph <-> ps ) $.
    syl2anb.2 $e |- ( ta <-> ch ) $.
    syl2anb.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference. $)
    syl2anb $p |- ( ( ph /\ ta ) -> th ) $=
      ( sylanb sylan2b ) EACDGABCDFHIJ $.
      $( [29-Jul-1999] $)
  $}

  ${
    syl2anbr.1 $e |- ( ps <-> ph ) $.
    syl2anbr.2 $e |- ( ch <-> ta ) $.
    syl2anbr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference. $)
    syl2anbr $p |- ( ( ph /\ ta ) -> th ) $=
      ( sylanbr sylan2br ) EACDGABCDFHIJ $.
      $( [29-Jul-1999] $)
  $}

  ${
    syland.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syland.2 $e |- ( ph -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism deduction. $)
    syland $p |- ( ph -> ( ( ps /\ th ) -> ta ) ) $=
      ( wi exp3a syld imp3a ) ABDEABCDEHFACDEGIJK $.
      $( [15-Dec-2004] $)
  $}

  ${
    sylan2d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan2d.2 $e |- ( ph -> ( ( th /\ ch ) -> ta ) ) $.
    $( A syllogism deduction. $)
    sylan2d $p |- ( ph -> ( ( th /\ ps ) -> ta ) ) $=
      ( ancomsd syland ) ABDEABCDEFADCEGHIH $.
      $( [15-Dec-2004] $)
  $}

  ${
    syl2and.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syl2and.2 $e |- ( ph -> ( th -> ta ) ) $.
    syl2and.3 $e |- ( ph -> ( ( ch /\ ta ) -> et ) ) $.
    $( A syllogism deduction. $)
    syl2and $p |- ( ph -> ( ( ps /\ th ) -> et ) ) $=
      ( sylan2d syland ) ABCDFGADECFHIJK $.
      $( [15-Dec-2004] $)
  $}

  ${
    biimpa.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Inference from a logical equivalence. $)
    biimpa $p |- ( ( ph /\ ps ) -> ch ) $=
      ( biimpd imp ) ABCABCDEF $.
      $( [3-May-1994] $)

    $( Inference from a logical equivalence. $)
    biimpar $p |- ( ( ph /\ ch ) -> ps ) $=
      ( biimprd imp ) ACBABCDEF $.
      $( [3-May-1994] $)

    $( Inference from a logical equivalence. $)
    biimpac $p |- ( ( ps /\ ph ) -> ch ) $=
      ( biimpcd imp ) BACABCDEF $.
      $( [3-May-1994] $)

    $( Inference from a logical equivalence. $)
    biimparc $p |- ( ( ch /\ ph ) -> ps ) $=
      ( biimprcd imp ) CABABCDEF $.
      $( [3-May-1994] $)
  $}

  $( Introduction of antecedent as conjunct.  Theorem *4.73 of
     [WhiteheadRussell] p. 121. $)
  iba $p |- ( ph -> ( ps <-> ( ps /\ ph ) ) ) $=
    ( wa pm3.21 simpl impbid1 ) ABBACABDBAEF $.
    $( [24-Mar-2013] $) $( [30-Mar-1994] $)

  $( Introduction of antecedent as conjunct. $)
  ibar $p |- ( ph -> ( ps <-> ( ph /\ ps ) ) ) $=
    ( wa pm3.2 simpr impbid1 ) ABABCABDABEF $.
    $( [24-Mar-2013] $) $( [5-Dec-1995] $)

  ${
    biantru.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth. $)
    biantru $p |- ( ps <-> ( ps /\ ph ) ) $=
      ( wa wb iba ax-mp ) ABBADECABFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    biantrur.1 $e |- ph $.
    $( A wff is equivalent to its conjunction with truth. $)
    biantrur $p |- ( ps <-> ( ph /\ ps ) ) $=
      ( wa wb ibar ax-mp ) ABABDECABFG $.
      $( [3-Aug-1994] $)
  $}

  ${
    biantrud.1 $e |- ( ph -> ps ) $.
    $( A wff is equivalent to its conjunction with truth.  (The proof was
       shortened by Wolf Lammen, 23-Oct-2013.) $)
    biantrud $p |- ( ph -> ( ch <-> ( ch /\ ps ) ) ) $=
      ( wa wb iba syl ) ABCCBEFDBCGH $.
      $( [23-Oct-2013] $) $( [2-Aug-1994] $)

    $( A wff is equivalent to its conjunction with truth.  (The proof was
       shortened by Andrew Salmon, 7-May-2011.) $)
    biantrurd $p |- ( ph -> ( ch <-> ( ps /\ ch ) ) ) $=
      ( wa wb ibar syl ) ABCBCEFDBCGH $.
      $( [12-May-2011] $) $( [1-May-1995] $)
  $}

  ${
    jca.1 $e |- ( ph -> ps ) $.
    jca.2 $e |- ( ph -> ch ) $.
    $( Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'").  (The proof was shortened by Wolf Lammen,
       25-Oct-2012.) $)
    jca $p |- ( ph -> ( ps /\ ch ) ) $=
      ( wa pm3.2 sylc ) ABCBCFDEBCGH $.
      $( [25-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    $( Deduction conjoining the consequents of two implications.  (The proof
       was shortened by Wolf Lammen, 23-Jul-2013.) $)
    jcad $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( wa pm3.2 syl6c ) ABCDCDGEFCDHI $.
      $( [23-Jul-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    jca31.1 $e |- ( ph -> ps ) $.
    jca31.2 $e |- ( ph -> ch ) $.
    jca31.3 $e |- ( ph -> th ) $.
    $( Join three consequents.  (Contributed by Jeff Hankins, 1-Aug-2009.) $)
    jca31 $p |- ( ph -> ( ( ps /\ ch ) /\ th ) ) $=
      ( wa jca ) ABCHDABCEFIGI $.
      $( [1-Aug-2009] $)

    $( Join three consequents.  (Contributed by FL, 1-Aug-2009.) $)
    jca32 $p |- ( ph -> ( ps /\ ( ch /\ th ) ) ) $=
      ( wa jca ) ABCDHEACDFGII $.
      $( [1-Aug-2009] $)
  $}

  ${
    jcai.1 $e |- ( ph -> ps ) $.
    jcai.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction replacing implication with conjunction. $)
    jcai $p |- ( ph -> ( ps /\ ch ) ) $=
      ( mpd jca ) ABCDABCDEFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    jctil.1 $e |- ( ph -> ps ) $.
    jctil.2 $e |- ch $.
    $( Inference conjoining a theorem to left of consequent in an
       implication. $)
    jctil $p |- ( ph -> ( ch /\ ps ) ) $=
      ( a1i jca ) ACBCAEFDG $.
      $( [31-Dec-1993] $)

    $( Inference conjoining a theorem to right of consequent in an
       implication. $)
    jctir $p |- ( ph -> ( ps /\ ch ) ) $=
      ( a1i jca ) ABCDCAEFG $.
      $( [31-Dec-1993] $)
  $}

  ${
    jctl.1 $e |- ps $.
    $( Inference conjoining a theorem to the left of a consequent.  (The proof
       was shortened by Wolf Lammen, 24-Oct-2012.) $)
    jctl $p |- ( ph -> ( ps /\ ph ) ) $=
      ( id jctil ) AABADCE $.
      $( [25-Oct-2012] $) $( [31-Dec-1993] $)

    $( Inference conjoining a theorem to the right of a consequent.  (The proof
       was shortened by Wolf Lammen, 24-Oct-2012.) $)
    jctr $p |- ( ph -> ( ph /\ ps ) ) $=
      ( id jctir ) AABADCE $.
      $( [25-Oct-2012] $) $( [18-Aug-1993] $)
  $}

  ${
    jctild.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctild.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to left of consequent in an
       implication. $)
    jctild $p |- ( ph -> ( ps -> ( th /\ ch ) ) ) $=
      ( a1d jcad ) ABDCADBFGEH $.
      $( [21-Apr-2005] $)
  $}

  ${
    jctird.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jctird.2 $e |- ( ph -> th ) $.
    $( Deduction conjoining a theorem to right of consequent in an
       implication. $)
    jctird $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
      ( a1d jcad ) ABCDEADBFGH $.
      $( [21-Apr-2005] $)
  $}

  $( Conjoin antecedent to left of consequent. $)
  ancl $p |- ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) ) $=
    ( wa pm3.2 a2i ) ABABCABDE $.
    $( [15-Aug-1994] $)

  $( Conjoin antecedent to left of consequent.  Theorem *4.7 of
     [WhiteheadRussell] p. 120.  (The proof was shortened by Wolf Lammen,
     24-Mar-2013.) $)
  anclb $p |- ( ( ph -> ps ) <-> ( ph -> ( ph /\ ps ) ) ) $=
    ( wa ibar pm5.74i ) ABABCABDE $.
    $( [24-Mar-2013] $) $( [25-Jul-1999] $)

  $( Theorem *5.42 of [WhiteheadRussell] p. 125. $)
  pm5.42 $p |- ( ( ph -> ( ps -> ch ) ) <->
                ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    ( wi wa ibar imbi2d pm5.74i ) ABCDBACEZDACIBACFGH $.
    $( [3-Jan-2005] $)

  $( Conjoin antecedent to right of consequent. $)
  ancr $p |- ( ( ph -> ps ) -> ( ph -> ( ps /\ ph ) ) ) $=
    ( wa pm3.21 a2i ) ABBACABDE $.
    $( [15-Aug-1994] $)

  $( Conjoin antecedent to right of consequent.  (The proof was shortened by
     Wolf Lammen, 24-Mar-2013.) $)
  ancrb $p |- ( ( ph -> ps ) <-> ( ph -> ( ps /\ ph ) ) ) $=
    ( wa iba pm5.74i ) ABBACABDE $.
    $( [24-Mar-2013] $) $( [25-Jul-1999] $)

  ${
    ancli.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to left of consequent. $)
    ancli $p |- ( ph -> ( ph /\ ps ) ) $=
      ( id jca ) AABADCE $.
      $( [12-Aug-1993] $)
  $}

  ${
    ancri.1 $e |- ( ph -> ps ) $.
    $( Deduction conjoining antecedent to right of consequent. $)
    ancri $p |- ( ph -> ( ps /\ ph ) ) $=
      ( id jca ) ABACADE $.
      $( [15-Aug-1994] $)
  $}

  ${
    ancld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (The proof was shortened by Wolf Lammen, 1-Nov-2012.) $)
    ancld $p |- ( ph -> ( ps -> ( ps /\ ch ) ) ) $=
      ( idd jcad ) ABBCABEDF $.
      $( [1-Nov-2012] $) $( [15-Aug-1994] $)
  $}

  ${
    ancrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication.  (The proof was shortened by Wolf Lammen, 1-Nov-2012.) $)
    ancrd $p |- ( ph -> ( ps -> ( ch /\ ps ) ) ) $=
      ( idd jcad ) ABCBDABEF $.
      $( [1-Nov-2012] $) $( [15-Aug-1994] $)
  $}

  $( Conjoin antecedent to left of consequent in nested implication.  (The
     proof was shortened by Wolf Lammen, 14-Jul-2013.) $)
  anc2l $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ph /\ ch ) ) ) ) $=
    ( wi wa pm5.42 biimpi ) ABCDDABACEDDABCFG $.
    $( [14-Jul-2013] $) $( [10-Aug-1994] $)

  $( Conjoin antecedent to right of consequent in nested implication. $)
  anc2r $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ch /\ ph ) ) ) ) $=
    ( wi wa pm3.21 imim2d a2i ) ABCDBCAEZDACIBACFGH $.
    $( [15-Aug-1994] $)

  ${
    anc2li.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (The proof was shortened by Wolf Lammen, 7-Dec-2012.) $)
    anc2li $p |- ( ph -> ( ps -> ( ph /\ ch ) ) ) $=
      ( id jctild ) ABCADAEF $.
      $( [7-Dec-2012] $) $( [10-Aug-1994] $)
  $}

  ${
    anc2ri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to right of consequent in nested
       implication.  (The proof was shortened by Wolf Lammen, 7-Dec-2012.) $)
    anc2ri $p |- ( ph -> ( ps -> ( ch /\ ph ) ) ) $=
      ( id jctird ) ABCADAEF $.
      $( [7-Dec-2012] $) $( [15-Aug-1994] $)
  $}

  $( Theorem *3.41 of [WhiteheadRussell] p. 113. $)
  pm3.41 $p |- ( ( ph -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wa simpl imim1i ) ABDACABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *3.42 of [WhiteheadRussell] p. 113. $)
  pm3.42 $p |- ( ( ps -> ch ) -> ( ( ph /\ ps ) -> ch ) ) $=
    ( wa simpr imim1i ) ABDBCABEF $.
    $( [3-Jan-2005] $)

  $( Conjunction implies implication.  Theorem *3.4 of [WhiteheadRussell]
     p. 113. $)
  pm3.4 $p |- ( ( ph /\ ps ) -> ( ph -> ps ) ) $=
    ( wa simpr a1d ) ABCBAABDE $.
    $( [31-Jul-1995] $)

  $( Conjunction with implication.  Compare Theorem *4.45 of [WhiteheadRussell]
     p. 119. $)
  pm4.45im $p |- ( ph <-> ( ph /\ ( ps -> ph ) ) ) $=
    ( wi wa ax-1 ancli simpl impbii ) AABACZDAIABEFAIGH $.
    $( [17-May-1998] $)

  ${
    anim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction.  (The proof was
       shortened by Wolf Lammen, 18-Dec-2013.) $)
    anim12d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ ta ) ) ) $=
      ( wa idd syl2and ) ABCDECEHZFGAKIJ $.
      $( [18-Dec-2013] $) $( [3-Apr-1994] $)
  $}

  ${
    anim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Add a conjunct to right of antecedent and consequent in a deduction. $)
    anim1d $p |- ( ph -> ( ( ps /\ th ) -> ( ch /\ th ) ) ) $=
      ( idd anim12d ) ABCDDEADFG $.
      $( [3-Apr-1994] $)

    $( Add a conjunct to left of antecedent and consequent in a deduction. $)
    anim2d $p |- ( ph -> ( ( th /\ ps ) -> ( th /\ ch ) ) ) $=
      ( idd anim12d ) ADDBCADFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    anim12i.1 $e |- ( ph -> ps ) $.
    anim12i.2 $e |- ( ch -> th ) $.
    $( Conjoin antecedents and consequents of two premises.  (The proof was
       shortened by Wolf Lammen, 14-Dec-2013.) $)
    anim12i $p |- ( ( ph /\ ch ) -> ( ps /\ th ) ) $=
      ( wa id syl2an ) ABDBDGZCEFJHI $.
      $( [14-Dec-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    anim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce conjunct to both sides of an implication. $)
    anim1i $p |- ( ( ph /\ ch ) -> ( ps /\ ch ) ) $=
      ( id anim12i ) ABCCDCEF $.
      $( [5-Aug-1993] $)

    $( Introduce conjunct to both sides of an implication. $)
    anim2i $p |- ( ( ch /\ ph ) -> ( ch /\ ps ) ) $=
      ( id anim12i ) CCABCEDF $.
      $( [5-Aug-1993] $)
  $}

  ${
    anim12ii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    anim12ii.2 $e |- ( th -> ( ps -> ta ) ) $.
    $( Conjoin antecedents and consequents in a deduction.  (The proof was
       shortened by Wolf Lammen, 19-Jul-2013.) $)
    anim12ii $p |- ( ( ph /\ th ) -> ( ps -> ( ch /\ ta ) ) ) $=
      ( wa wi adantr adantl jcad ) ADHBCEABCIDFJDBEIAGKL $.
      $( [19-Jul-2013] $) $( [11-Nov-2007] $)
  $}

  $( Theorem *3.47 of [WhiteheadRussell] p. 113.  It was proved by Leibniz, and
     it evidently pleased him enough to call it 'praeclarum theorema' (splendid
     theorem).  (The proof was shortened by Wolf Lammen, 7-Apr-2013.) $)
  prth $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) ->
              ( ( ph /\ ch ) -> ( ps /\ th ) ) ) $=
    ( wi wa simpl simpr anim12d ) ABEZCDEZFABCDJKGJKHI $.
    $( [7-Apr-2013] $) $( [12-Aug-1993] $)

  $( Theorem *3.33 (Syll) of [WhiteheadRussell] p. 112. $)
  pm3.33 $p |- ( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) ) $=
    ( wi imim1 imp ) ABDBCDACDABCEF $.
    $( [3-Jan-2005] $)

  $( Theorem *3.34 (Syll) of [WhiteheadRussell] p. 112. $)
  pm3.34 $p |- ( ( ( ps -> ch ) /\ ( ph -> ps ) ) -> ( ph -> ch ) ) $=
    ( wi imim2 imp ) BCDABDACDBCAEF $.
    $( [3-Jan-2005] $)

  $( Conjunctive detachment.  Theorem *3.35 of [WhiteheadRussell] p. 112. $)
  pm3.35 $p |- ( ( ph /\ ( ph -> ps ) ) -> ps ) $=
    ( wi pm2.27 imp ) AABCBABDE $.
    $( [14-Dec-2002] $)

  $( Theorem *5.31 of [WhiteheadRussell] p. 125. $)
  pm5.31 $p |- ( ( ch /\ ( ph -> ps ) ) -> ( ph -> ( ps /\ ch ) ) ) $=
    ( wi wa pm3.21 imim2d imp ) CABDABCEZDCBIACBFGH $.
    $( [3-Jan-2005] $)

  ${
    imp4.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( An importation inference. $)
    imp4a $p |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $=
      ( wi wa impexp syl6ibr ) ABCDEGGCDHEGFCDEIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp4b $p |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $=
      ( wa wi imp4a imp ) ABCDGEHABCDEFIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp4c $p |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $=
      ( wa wi imp3a ) ABCGDEABCDEHFII $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp4d $p |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $=
      ( wa imp4a imp3a ) ABCDGEABCDEFHI $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp41 $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $=
      ( wa wi imp imp31 ) ABGCDEABCDEHHFIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp42 $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $=
      ( wa wi imp32 imp ) ABCGGDEABCDEHFIJ $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp43 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $=
      ( wa imp4b imp ) ABGCDGEABCDEFHI $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp44 $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $=
      ( wa imp4c imp ) ABCGDGEABCDEFHI $.
      $( [26-Apr-1994] $)

    $( An importation inference. $)
    imp45 $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $=
      ( wa imp4d imp ) ABCDGGEABCDEFHI $.
      $( [26-Apr-1994] $)

  $}

  ${
    imp5.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $.
    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5a $p |- ( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) ) $=
      ( wi wa pm3.31 syl8 ) ABCDEFHHDEIFHGDEFJK $.
      $( [7-Jul-2009] $)

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5d $p |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) ) $=
      ( wa wi imp31 imp3a ) ABHCHDEFABCDEFIIGJK $.
      $( [7-Jul-2009] $)

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp5g $p |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) ) $=
      ( wa wi imp imp4c ) ABHCDEFABCDEFIIIGJK $.
      $( [7-Jul-2009] $)

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp55 $p |- ( ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) /\ ta ) -> et ) $=
      ( wa wi imp4a imp42 ) ABCDHEFABCDEFIGJK $.
      $( [7-Jul-2009] $)

    $( An importation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    imp511 $p |- ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et ) $=
      ( wa wi imp4a imp44 ) ABCDHEFABCDEFIGJK $.
      $( [7-Jul-2009] $)
  $}

  ${
    expimpd.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Exportation followed by a deduction version of importation. $)
    expimpd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( wi ex imp3a ) ABCDABCDFEGH $.
      $( [6-Sep-2008] $)
  $}

  ${
    exp31.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An exportation inference. $)
    exp31 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wi wa ex ) ABCDFABGCDEHH $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp32.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An exportation inference. $)
    exp32 $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( wa ex exp3a ) ABCDABCFDEGH $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4a.1 $e |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ) $.
    $( An exportation inference. $)
    exp4a $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa wi impexp syl6ib ) ABCDGEHCDEHHFCDEIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4b.1 $e |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ) $.
    $( An exportation inference.  (The proof was shortened by Wolf Lammen,
       23-Nov-2012.) $)
    exp4b $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa wi ex exp4a ) ABCDEABCDGEHFIJ $.
      $( [23-Nov-2012] $) $( [26-Apr-1994] $)
  $}

  ${
    exp4c.1 $e |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ) $.
    $( An exportation inference. $)
    exp4c $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp3a ) ABCDEGABCHDEFII $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp4d.1 $e |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ) $.
    $( An exportation inference. $)
    exp4d $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa exp3a exp4a ) ABCDEABCDGEFHI $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp41.1 $e |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $.
    $( An exportation inference. $)
    exp41 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa ex exp31 ) ABCDEGABHCHDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp42.1 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An exportation inference. $)
    exp42 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp31 exp3a ) ABCDEGABCHDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp43.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An exportation inference. $)
    exp43 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa ex exp4b ) ABCDEABGCDGEFHI $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp44.1 $e |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ) $.
    $( An exportation inference. $)
    exp44 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi wa exp32 exp3a ) ABCDEGABCHDEFIJ $.
      $( [26-Apr-1994] $)
  $}

  ${
    exp45.1 $e |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ) $.
    $( An exportation inference. $)
    exp45 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wa exp32 exp4a ) ABCDEABCDGEFHI $.
      $( [26-Apr-1994] $)
  $}

  ${
    expr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Export a wff from a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    expr $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi exp32 imp ) ABCDFABCDEGH $.
      $( [21-Feb-2011] $) $( [28-Aug-2009] $)
  $}

  ${
    exp5c.1 $e |- ( ph -> ( ( ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins, 7-Jul-2009.) $)
    exp5c $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi wa exp4a exp3a ) ABCDEFHHABCIDEFGJK $.
      $( [7-Jul-2009] $)
  $}

  ${
    exp53.1 $e |- ( ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) /\ ta ) -> et ) $.
    $( An exportation inference.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    exp53 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi wa ex exp43 ) ABCDEFHABICDIIEFGJK $.
      $( [21-Feb-2011] $) $( [7-Jul-2009] $)
  $}

  ${
    expl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Export a wff from a left conjunct.  (Contributed by Jeff Hankins,
       28-Aug-2009.) $)
    expl $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( exp31 imp3a ) ABCDABCDEFG $.
      $( [28-Aug-2009] $)
  $}

  ${
    impr.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Import a wff into a right conjunct.  (Contributed by Jeff Hankins,
       30-Aug-2009.) $)
    impr $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( wi ex imp32 ) ABCDABCDFEGH $.
      $( [21-Feb-2011] $) $( [28-Aug-2009] $)
  $}

  ${
    impl.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Export a wff from a left conjunct.  (Contributed by Mario Carneiro,
       9-Jul-2014.) $)
    impl $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( exp3a imp31 ) ABCDABCDEFG $.
      $( [9-Jul-2014] $)
  $}

  ${
    impac.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Importation with conjunction in consequent. $)
    impac $p |- ( ( ph /\ ps ) -> ( ch /\ ps ) ) $=
      ( wa ancrd imp ) ABCBEABCDFG $.
      $( [9-Aug-1994] $)
  $}

  ${
    exbiri.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Inference form of ~ exbir .  (Contributed by Alan Sare, 31-Dec-2011.)
       (The proof was shortened by Wolf Lammen, 27-Jan-2013.) $)
    exbiri $p |- ( ph -> ( ps -> ( th -> ch ) ) ) $=
      ( wa biimpar exp31 ) ABDCABFCDEGH $.
      $( [27-Jan-2013] $) $( [31-Dec-2011] $)
  $}

  ${
    pm3.26bda.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Deduction eliminating a conjunct. $)
    simprbda $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa biimpa simpld ) ABFCDABCDFEGH $.
      $( [22-Oct-2007] $)

    $( Deduction eliminating a conjunct. $)
    simplbda $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa biimpa simprd ) ABFCDABCDFEGH $.
      $( [22-Oct-2007] $)
  $}

  ${
    pm3.26bi2.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.
       (Contributed by Alan Sare, 31-Dec-2011.) $)
    simplbi2 $p |- ( ps -> ( ch -> ph ) ) $=
      ( wa biimpri ex ) BCAABCEDFG $.
      $( [31-Dec-2011] $)
  $}

  $( A theorem similar to the standard definition of the biconditional.
     Definition of [Margaris] p. 49. $)
  dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $=
    ( wb wi wa df-bi simpli simpri impbii ) ABCZABDBADEZJKDZKJDZABFZGLMNHI $.
    $( [31-Jan-2015] $) $( [5-Aug-1993] $)

  $( Definition ~ df-bi rewritten in an abbreviated form to help intuitive
     understanding of that definition.  Note that it is a conjunction of two
     implications; one which asserts properties that follow from the
     biconditional and one which asserts properties that imply the
     biconditional. $)
  dfbi $p |- ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
        /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $=
    ( wb wi wa dfbi2 biimpi biimpri pm3.2i ) ABCZABDBADEZDKJDJKABFZGJKLHI $.
    $( [15-Aug-2008] $)

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120.  (The proof was shortened by Wolf Lammen,
     2-Dec-2012.) $)
  pm4.71 $p |- ( ( ph -> ps ) <-> ( ph <-> ( ph /\ ps ) ) ) $=
    ( wa wi wb simpl biantru anclb dfbi2 3bitr4i ) AABCZDZLKADZCABDAKEMLABFGABH
    AKIJ $.
    $( [2-Dec-2012] $) $( [5-Aug-1993] $)

  $( Implication in terms of biconditional and conjunction.  Theorem *4.71 of
     [WhiteheadRussell] p. 120 (with conjunct reversed). $)
  pm4.71r $p |- ( ( ph -> ps ) <-> ( ph <-> ( ps /\ ph ) ) ) $=
    ( wi wa wb pm4.71 ancom bibi2i bitri ) ABCAABDZEABADZEABFJKAABGHI $.
    $( [25-Jul-1999] $)

  ${
    pm4.71i.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell]
       p. 120. $)
    pm4.71i $p |- ( ph <-> ( ph /\ ps ) ) $=
      ( wi wa wb pm4.71 mpbi ) ABDAABEFCABGH $.
      $( [4-Jan-2004] $)
  $}

  ${
    pm4.71ri.1 $e |- ( ph -> ps ) $.
    $( Inference converting an implication to a biconditional with
       conjunction.  Inference from Theorem *4.71 of [WhiteheadRussell] p. 120
       (with conjunct reversed). $)
    pm4.71ri $p |- ( ph <-> ( ps /\ ph ) ) $=
      ( wi wa wb pm4.71r mpbi ) ABDABAEFCABGH $.
      $( [1-Dec-2003] $)
  $}

  ${
    pm4.71rd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction converting an implication to a biconditional with
       conjunction.  Deduction from Theorem *4.71 of [WhiteheadRussell]
       p. 120. $)
    pm4.71rd $p |- ( ph -> ( ps <-> ( ch /\ ps ) ) ) $=
      ( wi wa wb pm4.71r sylib ) ABCEBCBFGDBCHI $.
      $( [10-Feb-2005] $)
  $}

  $( Theorem *4.24 of [WhiteheadRussell] p. 117. $)
  pm4.24 $p |- ( ph <-> ( ph /\ ph ) ) $=
    ( id pm4.71i ) AAABC $.
    $( [14-Mar-2014] $) $( [3-Jan-2005] $)

  $( Idempotent law for conjunction.  (The proof was shortened by Wolf Lammen,
     14-Mar-2014.) $)
  anidm $p |- ( ( ph /\ ph ) <-> ph ) $=
    ( wa pm4.24 bicomi ) AAABACD $.
    $( [14-Mar-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ anidm as of 14-Mar-2014. $)
  anidmOLD $p |- ( ( ph /\ ph ) <-> ph ) $=
    ( wa simpl id ancli impbii ) AABAAACAAADEF $.
    $( [6-Nov-2012] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ pm4.24 as of 14-Mar-2014. $)
  pm4.24OLD $p |- ( ph <-> ( ph /\ ph ) ) $=
    ( wa anidm bicomi ) AABAACD $.
    $( [3-Jan-2005] $)

  ${
    anidms.1 $e |- ( ( ph /\ ph ) -> ps ) $.
    $( Inference from idempotent law for conjunction. $)
    anidms $p |- ( ph -> ps ) $=
      ( ex pm2.43i ) ABAABCDE $.
      $( [15-Jun-1994] $)
  $}

  $( Conjunction idempotence with antecedent.  (Contributed by Roy F. Longton,
     8-Aug-2005.) $)
  anidmdbi $p |- ( ( ph -> ( ps /\ ps ) ) <-> ( ph -> ps ) ) $=
    ( wa anidm imbi2i ) BBCBABDE $.
    $( [8-Aug-2005] $)

  ${
    anasss.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism). $)
    anasss $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( exp31 imp32 ) ABCDABCDEFG $.
      $( [15-Nov-2002] $)
  $}

  ${
    anassrs.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Associative law for conjunction applied to antecedent (eliminates
       syllogism). $)
    anassrs $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( exp32 imp31 ) ABCDABCDEFG $.
      $( [15-Nov-2002] $)
  $}

  $( Associative law for conjunction.  Theorem *4.32 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Wolf Lammen, 24-Nov-2012.) $)
  anass $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    ( wa id anassrs anasss impbii ) ABDCDZABCDDZABCJJEFABCIIEGH $.
    $( [24-Nov-2012] $) $( [5-Aug-1993] $)

  ${
    sylanl1.1 $e |- ( ph -> ps ) $.
    sylanl1.2 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    sylanl1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa anim1i sylan ) ACHBCHDEABCFIGJ $.
      $( [10-Mar-2005] $)
  $}

  ${
    sylanl2.1 $e |- ( ph -> ch ) $.
    sylanl2.2 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    sylanl2 $p |- ( ( ( ps /\ ph ) /\ th ) -> ta ) $=
      ( wa anim2i sylan ) BAHBCHDEACBFIGJ $.
      $( [1-Jan-2005] $)
  $}

  ${
    sylanr1.1 $e |- ( ph -> ch ) $.
    sylanr1.2 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
    $( A syllogism inference. $)
    sylanr1 $p |- ( ( ps /\ ( ph /\ th ) ) -> ta ) $=
      ( wa anim1i sylan2 ) ADHBCDHEACDFIGJ $.
      $( [9-Apr-2005] $)
  $}

  ${
    sylanr2.1 $e |- ( ph -> th ) $.
    sylanr2.2 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
    $( A syllogism inference. $)
    sylanr2 $p |- ( ( ps /\ ( ch /\ ph ) ) -> ta ) $=
      ( wa anim2i sylan2 ) CAHBCDHEADCFIGJ $.
      $( [9-Apr-2005] $)
  $}

  ${
    sylani.1 $e |- ( ph -> ch ) $.
    sylani.2 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference. $)
    sylani $p |- ( ps -> ( ( ph /\ th ) -> ta ) ) $=
      ( wi a1i syland ) BACDEACHBFIGJ $.
      $( [2-May-1996] $)
  $}

  ${
    sylan2i.1 $e |- ( ph -> th ) $.
    sylan2i.2 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference. $)
    sylan2i $p |- ( ps -> ( ( ch /\ ph ) -> ta ) ) $=
      ( wi a1i sylan2d ) BADCEADHBFIGJ $.
      $( [1-Aug-1994] $)
  $}

  ${
    syl2ani.1 $e |- ( ph -> ch ) $.
    syl2ani.2 $e |- ( et -> th ) $.
    syl2ani.3 $e |- ( ps -> ( ( ch /\ th ) -> ta ) ) $.
    $( A syllogism inference. $)
    syl2ani $p |- ( ps -> ( ( ph /\ et ) -> ta ) ) $=
      ( sylan2i sylani ) ABCFEGFBCDEHIJK $.
      $( [3-Aug-1999] $)
  $}

  ${
    sylan9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents.  (The
       proof was shortened by Andrew Salmon, 7-May-2011.) $)
    sylan9 $p |- ( ( ph /\ th ) -> ( ps -> ta ) ) $=
      ( wi syl9 imp ) ADBEHABCDEFGIJ $.
      $( [12-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    sylan9r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylan9r.2 $e |- ( th -> ( ch -> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9r $p |- ( ( th /\ ph ) -> ( ps -> ta ) ) $=
      ( wi syl9r imp ) DABEHABCDEFGIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    syl2anc.1 $e |- ( ph -> ps ) $.
    syl2anc.2 $e |- ( ph -> ch ) $.
    syl2anc.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with contraction. $)
    syl2anc $p |- ( ph -> th ) $=
      ( ex sylc ) ABCDEFBCDGHI $.
      $( [16-Mar-2012] $)
  $}

  ${
    sylancl.1 $e |- ( ph -> ps ) $.
    sylancl.2 $e |- ch $.
    sylancl.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    sylancl $p |- ( ph -> th ) $=
      ( a1i syl2anc ) ABCDECAFHGI $.
      $( [18-Apr-2010] $) $( [2-Sep-2009] $)
  $}

  ${
    sylancr.1 $e |- ps $.
    sylancr.2 $e |- ( ph -> ch ) $.
    sylancr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( Syllogism inference combined with modus ponens.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    sylancr $p |- ( ph -> th ) $=
      ( a1i syl2anc ) ABCDBAEHFGI $.
      $( [2-Sep-2009] $)
  $}

  ${
    sylanbrc.1 $e |- ( ph -> ps ) $.
    sylanbrc.2 $e |- ( ph -> ch ) $.
    sylanbrc.3 $e |- ( th <-> ( ps /\ ch ) ) $.
    $( Syllogism inference.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    sylanbrc $p |- ( ph -> th ) $=
      ( wa jca sylibr ) ABCHDABCEFIGJ $.
      $( [11-Oct-2010] $) $( [2-Sep-2009] $)
  $}

  ${
    sylancb.1 $e |- ( ph <-> ps ) $.
    sylancb.2 $e |- ( ph <-> ch ) $.
    sylancb.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference combined with contraction. $)
    sylancb $p |- ( ph -> th ) $=
      ( syl2anb anidms ) ADABCDAEFGHI $.
      $( [3-Sep-2004] $)
  $}

  ${
    sylancbr.1 $e |- ( ps <-> ph ) $.
    sylancbr.2 $e |- ( ch <-> ph ) $.
    sylancbr.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A syllogism inference combined with contraction. $)
    sylancbr $p |- ( ph -> th ) $=
      ( syl2anbr anidms ) ADABCDAEFGHI $.
      $( [3-Sep-2004] $)
  $}

  ${
    sylancom.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    sylancom.2 $e |- ( ( ch /\ ps ) -> th ) $.
    $( Syllogism inference with commutation of antecents. $)
    sylancom $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa simpr syl2anc ) ABGCBDEABHFI $.
      $( [2-Jul-2008] $)
  $}

  ${
    mpdan.1 $e |- ( ph -> ps ) $.
    mpdan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 22-Nov-2012.) $)
    mpdan $p |- ( ph -> ch ) $=
      ( id syl2anc ) AABCAFDEG $.
      $( [22-Nov-2012] $) $( [23-May-1999] $)
  $}

  ${
    mpancom.1 $e |- ( ps -> ph ) $.
    mpancom.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens with commutation of antecedents.
       (The proof was shortened by Wolf Lammen, 7-Apr-2013.) $)
    mpancom $p |- ( ps -> ch ) $=
      ( id syl2anc ) BABCDBFEG $.
      $( [7-Apr-2013] $) $( [28-Oct-2003] $)
  $}

  ${
    mpan.1 $e |- ph $.
    mpan.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 7-Apr-2013.) $)
    mpan $p |- ( ps -> ch ) $=
      ( a1i mpancom ) ABCABDFEG $.
      $( [7-Apr-2013] $) $( [30-Aug-1993] $)
  $}

  ${
    mpan2.1 $e |- ps $.
    mpan2.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 19-Nov-2012.) $)
    mpan2 $p |- ( ph -> ch ) $=
      ( a1i mpdan ) ABCBADFEG $.
      $( [19-Nov-2012] $) $( [16-Sep-1993] $)
  $}

  ${
    mp2an.1 $e |- ph $.
    mp2an.2 $e |- ps $.
    mp2an.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( An inference based on modus ponens. $)
    mp2an $p |- ch $=
      ( mpan ax-mp ) BCEABCDFGH $.
      $( [13-Apr-1995] $)
  $}

  ${
    mp4an.1 $e |- ph $.
    mp4an.2 $e |- ps $.
    mp4an.3 $e |- ch $.
    mp4an.4 $e |- th $.
    mp4an.5 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens.  (Contributed by Jeff Madsen,
       15-Jun-2011.) $)
    mp4an $p |- ta $=
      ( wa pm3.2i mp2an ) ABKCDKEABFGLCDHILJM $.
      $( [15-Jun-2010] $)
  $}

  ${
    mpan2d.1 $e |- ( ph -> ch ) $.
    mpan2d.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens. $)
    mpan2d $p |- ( ph -> ( ps -> th ) ) $=
      ( exp3a mpid ) ABCDEABCDFGH $.
      $( [12-Dec-2004] $)
  $}

  ${
    mpand.1 $e |- ( ph -> ps ) $.
    mpand.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 7-Apr-2013.) $)
    mpand $p |- ( ph -> ( ch -> th ) ) $=
      ( ancomsd mpan2d ) ACBDEABCDFGH $.
      $( [7-Apr-2013] $) $( [12-Dec-2004] $)
  $}

  ${
    mpani.1 $e |- ps $.
    mpani.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 19-Nov-2012.) $)
    mpani $p |- ( ph -> ( ch -> th ) ) $=
      ( a1i mpand ) ABCDBAEGFH $.
      $( [19-Nov-2012] $) $( [10-Apr-1994] $)
  $}

  ${
    mpan2i.1 $e |- ch $.
    mpan2i.2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 19-Nov-2012.) $)
    mpan2i $p |- ( ph -> ( ps -> th ) ) $=
      ( a1i mpan2d ) ABCDCAEGFH $.
      $( [19-Nov-2012] $) $( [10-Apr-1994] $)
  $}

  ${
    mp2ani.1 $e |- ps $.
    mp2ani.2 $e |- ch $.
    mp2ani.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( An inference based on modus ponens. $)
    mp2ani $p |- ( ph -> th ) $=
      ( mpani mpi ) ACDFABCDEGHI $.
      $( [12-Dec-2004] $)
  $}

  ${
    mp2and.1 $e |- ( ph -> ps ) $.
    mp2and.2 $e |- ( ph -> ch ) $.
    mp2and.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( A deduction based on modus ponens. $)
    mp2and $p |- ( ph -> th ) $=
      ( mpand mpd ) ACDFABCDEGHI $.
      $( [12-Dec-2004] $)
  $}

  ${
    mpanl1.1 $e |- ph $.
    mpanl1.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 7-Apr-2013.) $)
    mpanl1 $p |- ( ( ps /\ ch ) -> th ) $=
      ( wa jctl sylan ) BABGCDBAEHFI $.
      $( [7-Apr-2013] $) $( [16-Aug-1994] $)
  $}

  ${
    mpanl2.1 $e |- ps $.
    mpanl2.2 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Andrew
       Salmon, 7-May-2011.) $)
    mpanl2 $p |- ( ( ph /\ ch ) -> th ) $=
      ( wa jctr sylan ) AABGCDABEHFI $.
      $( [22-Nov-2012] $) $( [16-Aug-1994] $)
  $}

  ${
    mpanl12.1 $e |- ph $.
    mpanl12.2 $e |- ps $.
    mpanl12.3 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanl12 $p |- ( ch -> th ) $=
      ( mpanl1 mpan ) BCDFABCDEGHI $.
      $( [13-Jul-2005] $)
  $}

  ${
    mpanr1.1 $e |- ps $.
    mpanr1.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Andrew
       Salmon, 7-May-2011.) $)
    mpanr1 $p |- ( ( ph /\ ch ) -> th ) $=
      ( anassrs mpanl2 ) ABCDEABCDFGH $.
      $( [12-May-2011] $) $( [3-May-1994] $)
  $}

  ${
    mpanr2.1 $e |- ch $.
    mpanr2.2 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Andrew
       Salmon, 7-May-2011.)  (The proof was shortened by Wolf Lammen,
       7-Apr-2013.) $)
    mpanr2 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa jctr sylan2 ) BABCGDBCEHFI $.
      $( [7-Apr-2013] $) $( [3-May-1994] $)

    $( Obsolete proof of ~ mpanr2 as of 7-Apr-2013.) $)
    mpanr2OLD $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa expr mpi ) ABGCDEABCDFHI $.
      $( [12-May-2011] $) $( [3-May-1994] $)
  $}

  ${
    mpanr12.1 $e |- ps $.
    mpanr12.2 $e |- ch $.
    mpanr12.3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpanr12 $p |- ( ph -> th ) $=
      ( mpanr1 mpan2 ) ACDFABCDEGHI $.
      $( [24-Jul-2009] $)
  $}

  ${
    mpanlr1.1 $e |- ps $.
    mpanlr1.2 $e |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens.  (The proof was shortened by Wolf
       Lammen, 7-Apr-2013.) $)
    mpanlr1 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa jctl sylanl2 ) CABCHDECBFIGJ $.
      $( [7-Apr-2013] $) $( [30-Dec-2004] $)
  $}

  ${
    pm5.74da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.74da $p |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ) $=
      ( wb ex pm5.74d ) ABCDABCDFEGH $.
      $( [4-May-2007] $)
  $}

  $( Distribution of implication with conjunction.  (The proof was shortened by
     Wolf Lammen, 6-Dec-2012.) $)
  imdistan $p |- ( ( ph -> ( ps -> ch ) ) <->
                ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    ( wi wa pm5.42 impexp bitr4i ) ABCDDABACEZDDABEIDABCFABIGH $.
    $( [6-Dec-2012] $) $( [31-May-1999] $)

  ${
    imdistani.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction. $)
    imdistani $p |- ( ( ph /\ ps ) -> ( ph /\ ch ) ) $=
      ( wa anc2li imp ) ABACEABCDFG $.
      $( [1-Aug-1994] $)
  $}

  ${
    imdistanri.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Distribution of implication with conjunction. $)
    imdistanri $p |- ( ( ps /\ ph ) -> ( ch /\ ph ) ) $=
      ( com12 impac ) BACABCDEF $.
      $( [8-Jan-2002] $)
  $}

  ${
    imdistand.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Distribution of implication with conjunction (deduction rule). $)
    imdistand $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $=
      ( wi wa imdistan sylib ) ABCDFFBCGBDGFEBCDHI $.
      $( [27-Aug-2004] $)
  $}

  ${
    imdistanda.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Distribution of implication with conjunction (deduction version with
       conjoined antecedent).  (Contributed by Jeff Madsen, 19-Jun-2011.) $)
    imdistanda $p |- ( ph -> ( ( ps /\ ch ) -> ( ps /\ th ) ) ) $=
      ( wi ex imdistand ) ABCDABCDFEGH $.
      $( [19-Jun-2011] $)
  $}

  ${
    pm5.32d.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.32d $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wa wb wi bi1 syl6 imdistand bi2 impbid ) ABCFBDFABCDABCDGZCDHECDIJKABDC
      ABNDCHECDLJKM $.
      $( [31-Jan-2015] $) $( [29-Oct-1996] $)

    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.32rd $p |- ( ph -> ( ( ch /\ ps ) <-> ( th /\ ps ) ) ) $=
      ( wa pm5.32d ancom 3bitr4g ) ABCFBDFCBFDBFABCDEGCBHDBHI $.
      $( [25-Dec-2004] $)
  $}

  ${
    pm5.32da.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Distribution of implication over biconditional (deduction rule). $)
    pm5.32da $p |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) ) $=
      ( wb ex pm5.32d ) ABCDABCDFEGH $.
      $( [9-Dec-2006] $)
  $}

  $( Distribution of implication over biconditional.  Theorem *5.32 of
     [WhiteheadRussell] p. 125. $)
  pm5.32 $p |- ( ( ph -> ( ps <-> ch ) ) <->
               ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    ( wb wi wa id pm5.32d ibar bibi12d biimprcd impbii ) ABCDZEZABFZACFZDZNABCN
    GHAMQABOCPABIACIJKL $.
    $( [31-Jan-2015] $) $( [1-Aug-1994] $)

  ${
    pm5.32i.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Distribution of implication over biconditional (inference rule). $)
    pm5.32i $p |- ( ( ph /\ ps ) <-> ( ph /\ ch ) ) $=
      ( wb wi wa pm5.32 mpbi ) ABCEFABGACGEDABCHI $.
      $( [1-Aug-1994] $)

    $( Distribution of implication over biconditional (inference rule). $)
    pm5.32ri $p |- ( ( ps /\ ph ) <-> ( ch /\ ph ) ) $=
      ( wa pm5.32i ancom 3bitr4i ) ABEACEBAECAEABCDFBAGCAGH $.
      $( [12-Mar-1995] $)
  $}

  ${
    biadan2.1 $e |- ( ph -> ps ) $.
    biadan2.2 $e |- ( ps -> ( ph <-> ch ) ) $.
    $( Add a conjunction to an equivalence.  (Contributed by Jeff Madsen,
       20-Jun-2011.) $)
    biadan2 $p |- ( ph <-> ( ps /\ ch ) ) $=
      ( wa pm4.71ri pm5.32i bitri ) ABAFBCFABDGBACEHI $.
      $( [20-Jun-2011] $)
  $}

  ${
    bi.aa $e |- ( ph <-> ps ) $.
    $( Introduce a left conjunct to both sides of a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 16-Nov-2013.) $)
    anbi2i $p |- ( ( ch /\ ph ) <-> ( ch /\ ps ) ) $=
      ( wb a1i pm5.32i ) CABABECDFG $.
      $( [16-Nov-2013] $) $( [5-Aug-1993] $)

    $( Introduce a right conjunct to both sides of a logical equivalence.  (The
       proof was shortened by Wolf Lammen, 16-Nov-2013.) $)
    anbi1i $p |- ( ( ph /\ ch ) <-> ( ps /\ ch ) ) $=
      ( wb a1i pm5.32ri ) CABABECDFG $.
      $( [16-Nov-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    anbi12.1 $e |- ( ph <-> ps ) $.
    anbi12.2 $e |- ( ch <-> th ) $.
    $( Conjoin both sides of two equivalences. $)
    anbi12i $p |- ( ( ph /\ ch ) <-> ( ps /\ th ) ) $=
      ( wa anbi1i anbi2i bitri ) ACGBCGBDGABCEHCDBFIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    sylan9bb.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bb.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9bb $p |- ( ( ph /\ th ) -> ( ps <-> ta ) ) $=
      ( wa wb adantr adantl bitrd ) ADHBCEABCIDFJDCEIAGKL $.
      $( [4-Mar-1995] $)
  $}

  ${
    sylan9bbr.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    sylan9bbr.2 $e |- ( th -> ( ch <-> ta ) ) $.
    $( Nested syllogism inference conjoining dissimilar antecedents. $)
    sylan9bbr $p |- ( ( th /\ ph ) -> ( ps <-> ta ) ) $=
      ( wb sylan9bb ancoms ) ADBEHABCDEFGIJ $.
      $( [4-Mar-1995] $)
  $}

  ${
    anbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding a left conjunct to both sides of a logical
       equivalence.  (The proof was shortened by Wolf Lammen, 16-Nov-2013.) $)
    anbi2d $p |- ( ph -> ( ( th /\ ps ) <-> ( th /\ ch ) ) ) $=
      ( wb a1d pm5.32d ) ADBCABCFDEGH $.
      $( [16-Nov-2013] $) $( [5-Aug-1993] $)

    $( Deduction adding a right conjunct to both sides of a logical
       equivalence.  (The proof was shortened by Wolf Lammen, 16-Nov-2013.) $)
    anbi1d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ th ) ) ) $=
      ( wb a1d pm5.32rd ) ADBCABCFDEGH $.
      $( [16-Nov-2013] $) $( [5-Aug-1993] $)
  $}

  $( Introduce a right conjunct to both sides of a logical equivalence.
     Theorem *4.36 of [WhiteheadRussell] p. 118. $)
  anbi1 $p |- ( ( ph <-> ps ) -> ( ( ph /\ ch ) <-> ( ps /\ ch ) ) ) $=
    ( wb id anbi1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  $( Introduce a left conjunct to both sides of a logical equivalence. $)
  anbi2 $p |- ( ( ph <-> ps ) -> ( ( ch /\ ph ) <-> ( ch /\ ps ) ) ) $=
    ( wb id anbi2d ) ABDZABCGEF $.
    $( [16-Nov-2013] $)

  $( Theorem *4.22 of [WhiteheadRussell] p. 117. $)
  bitr $p |- ( ( ( ph <-> ps ) /\ ( ps <-> ch ) ) -> ( ph <-> ch ) ) $=
    ( wb bibi1 biimpar ) ABDACDBCDABCEF $.
    $( [3-Jan-2005] $)

  ${
    anbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    anbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of
       conjunctions. $)
    anbi12d $p |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) ) $=
      ( wa anbi1d anbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *5.3 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Andrew Salmon, 7-May-2011.) $)
  pm5.3 $p |- ( ( ( ph /\ ps ) -> ch ) <->
               ( ( ph /\ ps ) -> ( ph /\ ch ) ) ) $=
    ( wa wi impexp imdistan bitri ) ABDZCEABCEEIACDEABCFABCGH $.
    $( [12-May-2011] $) $( [3-Jan-2005] $)

  ${
    adant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 24-Nov-2012.) $)
    adantll $p |- ( ( ( th /\ ph ) /\ ps ) -> ch ) $=
      ( wa simpr sylan ) DAFABCDAGEH $.
      $( [24-Nov-2012] $) $( [4-May-1994] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 24-Nov-2012.) $)
    adantlr $p |- ( ( ( ph /\ th ) /\ ps ) -> ch ) $=
      ( wa simpl sylan ) ADFABCADGEH $.
      $( [24-Nov-2012] $) $( [4-May-1994] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 24-Nov-2012.) $)
    adantrl $p |- ( ( ph /\ ( th /\ ps ) ) -> ch ) $=
      ( wa simpr sylan2 ) DBFABCDBGEH $.
      $( [24-Nov-2012] $) $( [4-May-1994] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 24-Nov-2012.) $)
    adantrr $p |- ( ( ph /\ ( ps /\ th ) ) -> ch ) $=
      ( wa simpl sylan2 ) BDFABCBDGEH $.
      $( [24-Nov-2012] $) $( [4-May-1994] $)
  $}

  ${
    adantl2.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 2-Dec-2012.) $)
    adantlll $p |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th ) $=
      ( wa simpr sylanl1 ) EAGABCDEAHFI $.
      $( [2-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantllr $p |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th ) $=
      ( wa simpl sylanl1 ) AEGABCDAEHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantlrl $p |- ( ( ( ph /\ ( ta /\ ps ) ) /\ ch ) -> th ) $=
      ( wa simpr sylanl2 ) EBGABCDEBHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantlrr $p |- ( ( ( ph /\ ( ps /\ ta ) ) /\ ch ) -> th ) $=
      ( wa simpl sylanl2 ) BEGABCDBEHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)
  $}

  ${
    adantr2.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantrll $p |- ( ( ph /\ ( ( ta /\ ps ) /\ ch ) ) -> th ) $=
      ( wa simpr sylanr1 ) EBGABCDEBHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantrlr $p |- ( ( ph /\ ( ( ps /\ ta ) /\ ch ) ) -> th ) $=
      ( wa simpl sylanr1 ) BEGABCDBEHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantrrl $p |- ( ( ph /\ ( ps /\ ( ta /\ ch ) ) ) -> th ) $=
      ( wa simpr sylanr2 ) ECGABCDECHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)

    $( Deduction adding a conjunct to antecedent.  (The proof was shortened by
       Wolf Lammen, 4-Dec-2012.) $)
    adantrrr $p |- ( ( ph /\ ( ps /\ ( ch /\ ta ) ) ) -> th ) $=
      ( wa simpl sylanr2 ) CEGABCDCEHFI $.
      $( [4-Dec-2012] $) $( [26-Dec-2004] $)
  $}

  ${
    ad2ant.1 $e |- ( ph -> ps ) $.
    $( Deduction adding conjuncts to antecedent.  (The proof was shortened by
       Wolf Lammen, 20-Nov-2012.) $)
    ad2antrr $p |- ( ( ( ph /\ ch ) /\ th ) -> ps ) $=
      ( adantr adantlr ) ADBCABDEFG $.
      $( [20-Nov-2012] $) $( [19-Oct-1999] $)

    $( Deduction adding 3 conjuncts to antecedent. $)
    ad3antrrr $p |- ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) -> ps ) $=
      ( wa adantr ad2antrr ) ACGBDEABCFHI $.
      $( [28-Jul-2012] $)

    $( Deduction adding conjuncts to antecedent.  (The proof was shortened by
       Wolf Lammen, 20-Nov-2012.) $)
    ad2antlr $p |- ( ( ( ch /\ ph ) /\ th ) -> ps ) $=
      ( adantr adantll ) ADBCABDEFG $.
      $( [20-Nov-2012] $) $( [19-Oct-1999] $)

    $( Deduction adding conjuncts to antecedent. $)
    ad2antrl $p |- ( ( ch /\ ( ph /\ th ) ) -> ps ) $=
      ( wa adantr adantl ) ADFBCABDEGH $.
      $( [19-Oct-1999] $)

    $( Deduction adding conjuncts to antecedent. $)
    ad2antll $p |- ( ( ch /\ ( th /\ ph ) ) -> ps ) $=
      ( wa adantl ) DAFBCABDEGG $.
      $( [19-Oct-1999] $)
  $}

  ${
    ad2ant2.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2l $p |- ( ( ( th /\ ph ) /\ ( ta /\ ps ) ) -> ch ) $=
      ( wa adantrl adantll ) AEBGCDABCEFHI $.
      $( [8-Jan-2006] $)

    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2r $p |- ( ( ( ph /\ th ) /\ ( ps /\ ta ) ) -> ch ) $=
      ( wa adantrr adantlr ) ABEGCDABCEFHI $.
      $( [8-Jan-2006] $)

    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2lr $p |- ( ( ( th /\ ph ) /\ ( ps /\ ta ) ) -> ch ) $=
      ( wa adantrr adantll ) ABEGCDABCEFHI $.
      $( [23-Nov-2007] $)

    $( Deduction adding two conjuncts to antecedent. $)
    ad2ant2rl $p |- ( ( ( ph /\ th ) /\ ( ta /\ ps ) ) -> ch ) $=
      ( wa adantrl adantlr ) AEBGCDABCEFHI $.
      $( [24-Nov-2007] $)
  $}

  $( Simplification of a conjunction. $)
  simpll $p |- ( ( ( ph /\ ps ) /\ ch ) -> ph ) $=
    ( id ad2antrr ) AABCADE $.
    $( [18-Mar-2007] $)

  $( Simplification of a conjunction. $)
  simplr $p |- ( ( ( ph /\ ps ) /\ ch ) -> ps ) $=
    ( id ad2antlr ) BBACBDE $.
    $( [20-Mar-2007] $)

  $( Simplification of a conjunction. $)
  simprl $p |- ( ( ph /\ ( ps /\ ch ) ) -> ps ) $=
    ( id ad2antrl ) BBACBDE $.
    $( [21-Mar-2007] $)

  $( Simplification of a conjunction. $)
  simprr $p |- ( ( ph /\ ( ps /\ ch ) ) -> ch ) $=
    ( id ad2antll ) CCABCDE $.
    $( [21-Mar-2007] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ph ) $=
    ( wa simpl ad2antrr ) ABEACDABFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simpllr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ps ) $=
    ( wa simpr ad2antrr ) ABEBCDABFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrl $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ps ) $=
    ( wa simpl ad2antlr ) BCEBADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simplrr $p |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ch ) $=
    ( wa simpr ad2antlr ) BCECADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprll $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ps ) $=
    ( wa simpl ad2antrl ) BCEBADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprlr $p |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ch ) $=
    ( wa simpr ad2antrl ) BCECADBCFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrl $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ch ) $=
    ( wa simpl ad2antll ) CDECABCDFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Simplification of a conjunction.  (Contributed by Jeff Hankins,
     28-Jul-2009.) $)
  simprrr $p |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> th ) $=
    ( wa simpr ad2antll ) CDEDABCDFG $.
    $( [18-Apr-2010] $) $( [28-Jul-2009] $)

  $( Theorem *4.87 of [WhiteheadRussell] p. 122.  (The proof was shortened by
     Eric Schmidt, 26-Oct-2006.) $)
  pm4.87 $p |- ( ( ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) /\
                ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) ) /\
                ( ( ps -> ( ph -> ch ) ) <-> ( ( ps /\ ph ) -> ch ) ) ) $=
    ( wa wi wb impexp bi2.04 pm3.2i bicomi ) ABDCEABCEEZFZKBACEEZFZDMBADCEZFLNA
    BCGABCHIOMBACGJI $.
    $( [27-Oct-2006] $) $( [3-Jan-2005] $)

  $( Introduce one conjunct as an antecedent to the other.  "abai" stands for
     "and, biconditional, and, implication".  (The proof was shortened by Wolf
     Lammen, 7-Dec-2012.) $)
  abai $p |- ( ( ph /\ ps ) <-> ( ph /\ ( ph -> ps ) ) ) $=
    ( wi biimt pm5.32i ) ABABCABDE $.
    $( [7-Dec-2012] $) $( [12-Aug-1993] $)

  $( Swap two conjuncts.  Note that the first digit (1) in the label refers to
     the outer conjunct position, and the next digit (2) to the inner conjunct
     position. $)
  an12 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ps /\ ( ph /\ ch ) ) ) $=
    ( wa ancom anbi1i anass 3bitr3i ) ABDZCDBADZCDABCDDBACDDIJCABEFABCGBACGH $.
    $( [12-Mar-1995] $)

  $( A rearrangement of conjuncts.  (The proof was shortened by Wolf Lammen,
     25-Dec-2012.) $)
  an32 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $=
    ( wa anass an12 ancom 3bitri ) ABDCDABCDDBACDZDIBDABCEABCFBIGH $.
    $( [25-Dec-2012] $) $( [12-Mar-1995] $)

  $( A rearrangement of conjuncts.  (The proof was shortened by Wolf Lammen,
     31-Dec-2012.) $)
  an13 $p |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ch /\ ( ps /\ ph ) ) ) $=
    ( wa an12 anass ancom 3bitr2i ) ABCDDBACDDBADZCDCIDABCEBACFICGH $.
    $( [31-Dec-2012] $) $( [24-Jun-2012] $)

  $( A rearrangement of conjuncts.  (The proof was shortened by Wolf Lammen,
     31-Dec-2012.) $)
  an31 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ch /\ ps ) /\ ph ) ) $=
    ( wa an13 anass 3bitr4i ) ABCDDCBADDABDCDCBDADABCEABCFCBAFG $.
    $( [31-Dec-2012] $) $( [24-Jun-2012] $)

  ${
    an12s.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Swap two conjuncts in antecedent.  The label suffix "s" means that
       ~ an12 is combined with ~ syl (or a variant). $)
    an12s $p |- ( ( ps /\ ( ph /\ ch ) ) -> th ) $=
      ( wa an12 sylbi ) BACFFABCFFDBACGEH $.
      $( [13-Mar-1996] $)

    $( Inference commuting a nested conjunction in antecedent.  (The proof was
       shortened by Wolf Lammen, 24-Nov-2012.) $)
    ancom2s $p |- ( ( ph /\ ( ch /\ ps ) ) -> th ) $=
      ( wa pm3.22 sylan2 ) CBFABCFDCBGEH $.
      $( [24-Nov-2012] $) $( [24-May-2006] $)

    $( Swap two conjuncts in antecedent. $)
    an13s $p |- ( ( ch /\ ( ps /\ ph ) ) -> th ) $=
      ( exp32 com13 imp32 ) CBADABCDABCDEFGH $.
      $( [31-May-2006] $)
  $}

  ${
    an32s.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Swap two conjuncts in antecedent. $)
    an32s $p |- ( ( ( ph /\ ch ) /\ ps ) -> th ) $=
      ( wa an32 sylbi ) ACFBFABFCFDACBGEH $.
      $( [13-Mar-1996] $)

    $( Inference commuting a nested conjunction in antecedent.  (The proof was
       shortened by Wolf Lammen, 24-Nov-2012.) $)
    ancom1s $p |- ( ( ( ps /\ ph ) /\ ch ) -> th ) $=
      ( wa pm3.22 sylan ) BAFABFCDBAGEH $.
      $( [24-Nov-2012] $) $( [24-May-2006] $)

    $( Swap two conjuncts in antecedent. $)
    an31s $p |- ( ( ( ch /\ ps ) /\ ph ) -> th ) $=
      ( exp31 com13 imp31 ) CBADABCDABCDEFGH $.
      $( [31-May-2006] $)
  $}

  $( Absorption into embedded conjunct.  (The proof was shortened by Wolf
     Lammen, 16-Nov-2013.) $)
  anabs1 $p |- ( ( ( ph /\ ps ) /\ ph ) <-> ( ph /\ ps ) ) $=
    ( wa simpl pm4.71i bicomi ) ABCZGACGAABDEF $.
    $( [16-Nov-2013] $) $( [4-Sep-1995] $)

  $( Absorption into embedded conjunct.  (The proof was shortened by Wolf
     Lammen, 9-Dec-2012.) $)
  anabs5 $p |- ( ( ph /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    ( wa ibar bicomd pm5.32i ) AABCZBABGABDEF $.
    $( [9-Dec-2012] $) $( [20-Jul-1996] $)

  $( Absorption into embedded conjunct.  (The proof was shortened by Wolf
     Lammen, 17-Nov-2013.) $)
  anabs7 $p |- ( ( ps /\ ( ph /\ ps ) ) <-> ( ph /\ ps ) ) $=
    ( wa simpr pm4.71ri bicomi ) ABCZBGCGBABDEF $.
    $( [17-Nov-2013] $) $( [20-Jul-1996] $)

  ${
    anabsan.1 $e |- ( ( ( ph /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent with conjunction. $)
    anabsan $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa pm4.24 sylanb ) AAAEBCAFDG $.
      $( [18-Nov-2013] $) $( [24-Mar-1996] $)
  $}

  ${
    anabss1.1 $e |- ( ( ( ph /\ ps ) /\ ph ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 31-Dec-2012.) $)
    anabss1 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( an32s anabsan ) ABCABACDEF $.
      $( [19-Nov-2013] $) $( [20-Jul-1996] $)
  $}

  ${
    anabss4.1 $e |- ( ( ( ps /\ ph ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction. $)
    anabss4 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabss1 ancoms ) BACBACDEF $.
      $( [20-Jul-1996] $)
  $}

  ${
    anabss5.1 $e |- ( ( ph /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 1-Jan-2013.) $)
    anabss5 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anassrs anabsan ) ABCAABCDEF $.
      $( [1-Jan-2013] $) $( [10-May-1994] $)
  $}

  ${
    anabsi5.1 $e |- ( ph -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 18-Nov-2013.) $)
    anabsi5 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( wa imp anabss5 ) ABCAABECDFG $.
      $( [18-Nov-2013] $) $( [11-Jun-1995] $)
  $}

  ${
    anabsi6.1 $e |- ( ph -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction. $)
    anabsi6 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( ancomsd anabsi5 ) ABCABACDEF $.
      $( [14-Aug-2000] $)
  $}

  ${
    anabsi7.1 $e |- ( ps -> ( ( ph /\ ps ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 18-Nov-2013.) $)
    anabsi7 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabsi6 ancoms ) BACBACDEF $.
      $( [18-Nov-2013] $) $( [20-Jul-1996] $)
  $}

  ${
    anabsi8.1 $e |- ( ps -> ( ( ps /\ ph ) -> ch ) ) $.
    $( Absorption of antecedent into conjunction. $)
    anabsi8 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anabsi5 ancoms ) BACBACDEF $.
      $( [26-Sep-1999] $)
  $}

  ${
    anabss7.1 $e |- ( ( ps /\ ( ph /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 19-Nov-2013.) $)
    anabss7 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anassrs anabss4 ) ABCBABCDEF $.
      $( [19-Nov-2013] $) $( [20-Jul-1996] $)
  $}

  ${
    anabsan2.1 $e |- ( ( ph /\ ( ps /\ ps ) ) -> ch ) $.
    $( Absorption of antecedent with conjunction. $)
    anabsan2 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( an12s anabss7 ) ABCABBCDEF $.
      $( [1-Jan-2013] $) $( [10-May-2004] $)
  $}

  ${
    anabss3.1 $e |- ( ( ( ph /\ ps ) /\ ps ) -> ch ) $.
    $( Absorption of antecedent into conjunction.  (The proof was shortened by
       Wolf Lammen, 1-Jan-2013.) $)
    anabss3 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( anasss anabsan2 ) ABCABBCDEF $.
      $( [1-Jan-2013] $) $( [20-Jul-1996] $)
  $}

  $( Rearrangement of 4 conjuncts. $)
  an4 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
              ( ( ph /\ ch ) /\ ( ps /\ th ) ) ) $=
    ( wa an12 anbi2i anass 3bitr4i ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHAC
    LHI $.
    $( [10-Jul-1994] $)

  $( Rearrangement of 4 conjuncts. $)
  an42 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                 ( ( ph /\ ch ) /\ ( th /\ ps ) ) ) $=
    ( wa an4 ancom anbi2i bitri ) ABECDEEACEZBDEZEJDBEZEABCDFKLJBDGHI $.
    $( [7-Feb-1996] $)

  ${
    an4s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent. $)
    an4s $p |- ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) -> ta ) $=
      ( wa an4 sylbi ) ACGBDGGABGCDGGEACBDHFI $.
      $( [10-Aug-1995] $)
  $}

  ${
    an41r3s.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $.
    $( Inference rearranging 4 conjuncts in antecedent. $)
    an42s $p |- ( ( ( ph /\ ch ) /\ ( th /\ ps ) ) -> ta ) $=
      ( wa an4s ancom2s ) ACGBDEABCDEFHI $.
      $( [10-Aug-1995] $)
  $}

  $( Distribution of conjunction over conjunction. $)
  anandi $p |- ( ( ph /\ ( ps /\ ch ) ) <->
               ( ( ph /\ ps ) /\ ( ph /\ ch ) ) ) $=
    ( wa anidm anbi1i an4 bitr3i ) ABCDZDAADZIDABDACDDJAIAEFAABCGH $.
    $( [14-Aug-1995] $)

  $( Distribution of conjunction over conjunction. $)
  anandir $p |- ( ( ( ph /\ ps ) /\ ch ) <->
               ( ( ph /\ ch ) /\ ( ps /\ ch ) ) ) $=
    ( wa anidm anbi2i an4 bitr3i ) ABDZCDICCDZDACDBCDDJCICEFABCCGH $.
    $( [24-Aug-1995] $)

  ${
    anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent. $)
    anandis $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      ( wa an4s anabsan ) ABCFDABACDEGH $.
      $( [7-Jun-2004] $)
  $}

  ${
    anandirs.1 $e |- ( ( ( ph /\ ch ) /\ ( ps /\ ch ) ) -> ta ) $.
    $( Inference that undistributes conjunction in the antecedent. $)
    anandirs $p |- ( ( ( ph /\ ps ) /\ ch ) -> ta ) $=
      ( wa an4s anabsan2 ) ABFCDACBCDEGH $.
      $( [7-Jun-2004] $)
  $}

  ${
    impbida.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    impbida.2 $e |- ( ( ph /\ ch ) -> ps ) $.
    $( Deduce an equivalence from two implications. $)
    impbida $p |- ( ph -> ( ps <-> ch ) ) $=
      ( ex impbid ) ABCABCDFACBEFG $.
      $( [17-Feb-2007] $)
  $}

  $( Theorem *3.45 (Fact) of [WhiteheadRussell] p. 113. $)
  pm3.45 $p |- ( ( ph -> ps ) -> ( ( ph /\ ch ) -> ( ps /\ ch ) ) ) $=
    ( wi id anim1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  ${
    im2an9.1 $e |- ( ph -> ( ps -> ch ) ) $.
    im2an9.2 $e |- ( th -> ( ta -> et ) ) $.
    $( Deduction joining nested implications to form implication of
       conjunctions. $)
    im2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      ( wa wi adantr adantl anim12d ) ADIBCEFABCJDGKDEFJAHLM $.
      $( [29-Feb-1996] $)

    $( Deduction joining nested implications to form implication of
       conjunctions. $)
    im2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) ) $=
      ( wa wi im2anan9 ancoms ) ADBEICFIJABCDEFGHKL $.
      $( [29-Feb-1996] $)
  $}

  ${
    anim12dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    anim12dan.2 $e |- ( ( ph /\ th ) -> ta ) $.
    $( Conjoin antecedents and consequents in a deduction.  (Contributed by
       Mario Carneiro, 12-May-2014.) $)
    anim12dan $p |- ( ( ph /\ ( ps /\ th ) ) -> ( ch /\ ta ) ) $=
      ( wa ex anim12d imp ) ABDHCEHABCDEABCFIADEGIJK $.
      $( [12-May-2014] $)
  $}

  $( Two propositions are equivalent if they are both true.  Theorem *5.1 of
     [WhiteheadRussell] p. 123. $)
  pm5.1 $p |- ( ( ph /\ ps ) -> ( ph <-> ps ) ) $=
    ( wb pm5.501 biimpa ) ABABCABDE $.
    $( [21-May-1994] $)

  $( Theorem *3.43 (Comp) of [WhiteheadRussell] p. 113. $)
  pm3.43 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wi wa pm3.43i imp ) ABDACDABCEDABCFG $.
    $( [27-Nov-2013] $) $( [3-Jan-2005] $)

  $( Distributive law for implication over conjunction.  Compare Theorem *4.76
     of [WhiteheadRussell] p. 121.  (The proof was shortened by Wolf Lammen,
     27-Nov-2013.) $)
  jcab $p |- ( ( ph -> ( ps /\ ch ) ) <->
                ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $=
    ( wa wi simpl imim2i simpr jca pm3.43 impbii ) ABCDZEZABEZACEZDMNOLBABCFGLC
    ABCHGIABCJK $.
    $( [27-Nov-2013] $) $( [3-Apr-1994] $)

  $( Obsolete proof of ~ pm3.43 as of 27-Nov-2013 $)
  pm3.43OLD $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wa wi jcab biimpri ) ABCDEABEACEDABCFG $.
    $( [3-Jan-2005] $)

  $( Theorem *4.76 of [WhiteheadRussell] p. 121. $)
  pm4.76 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <->
                ( ph -> ( ps /\ ch ) ) ) $=
    ( wa wi jcab bicomi ) ABCDEABEACEDABCFG $.
    $( [3-Jan-2005] $)

  $( Theorem *4.38 of [WhiteheadRussell] p. 118. $)
  pm4.38 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph /\ ps ) <-> ( ch /\ th ) ) ) $=
    ( wb wa simpl simpr anbi12d ) ACEZBDEZFACBDJKGJKHI $.
    $( [3-Jan-2005] $)

  ${
    bi2an9.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi2an9.2 $e |- ( th -> ( ta <-> et ) ) $.
    $( Deduction joining two equivalences to form equivalence of
       conjunctions. $)
    bi2anan9 $p |- ( ( ph /\ th ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      ( wa anbi1d anbi2d sylan9bb ) ABEICEIDCFIABCEGJDEFCHKL $.
      $( [31-Jul-1995] $)

    $( Deduction joining two equivalences to form equivalence of
       conjunctions. $)
    bi2anan9r $p |- ( ( th /\ ph ) -> ( ( ps /\ ta ) <-> ( ch /\ et ) ) ) $=
      ( wa wb bi2anan9 ancoms ) ADBEICFIJABCDEFGHKL $.
      $( [19-Feb-1996] $)

    $( Deduction joining two biconditionals with different antecedents. $)
    bi2bian9 $p |- ( ( ph /\ th ) -> ( ( ps <-> ta ) <-> ( ch <-> et ) ) ) $=
      ( wa wb adantr adantl bibi12d ) ADIBCEFABCJDGKDEFJAHLM $.
      $( [12-May-2004] $)
  $}

  $( Theorem *5.33 of [WhiteheadRussell] p. 125. $)
  pm5.33 $p |- ( ( ph /\ ( ps -> ch ) ) <->
                ( ph /\ ( ( ph /\ ps ) -> ch ) ) ) $=
    ( wi wa ibar imbi1d pm5.32i ) ABCDABEZCDABICABFGH $.
    $( [3-Jan-2005] $)

  $( Theorem *5.36 of [WhiteheadRussell] p. 125. $)
  pm5.36 $p |- ( ( ph /\ ( ph <-> ps ) ) <-> ( ps /\ ( ph <-> ps ) ) ) $=
    ( wb id pm5.32ri ) ABCZABFDE $.
    $( [3-Jan-2005] $)

  ${
    bianabs.1 $e |- ( ph -> ( ps <-> ( ph /\ ch ) ) ) $.
    $( Absorb a hypothesis into the second member of a biconditional.
       (Contributed by FL, 15-Feb-2007.) $)
    bianabs $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wa ibar bitr4d ) ABACECDACFG $.
      $( [22-May-2008] $) $( [15-Feb-2007] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical negation (intuitionistic)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( 'Not' introduction.  Axiom 4 of 10 for intuitionistic logic. $)
  ax-in1 $a |- ( ( ph -> -. ph ) -> -. ph ) $.

  $( 'Not' elimination.  Axiom 5 of 10 for intuitionistic logic. $)
  ax-in2 $a |- ( -. ph -> ( ph -> ps ) ) $.

  $( Reductio ad absurdum.  Theorem *2.01 of [WhiteheadRussell] p. 100.  (The
     proof was shortened by O'Cat, 21-Nov-2008.)  (The proof was shortened by
     Wolf Lammen, 31-Oct-2012.) $)
  pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    ( ax-in1 ) AB $.
    $( [31-Oct-2012] $) $( [18-Aug-1993] $)

  $( From a wff and its negation, anything is true.  Theorem *2.21 of
     [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  (The proof
     was shortened by Wolf Lammen, 14-Sep-2012.) $)
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( ax-in2 ) ABC $.
    $( [31-Jan-2015] $) $( [5-Aug-1993] $)

  ${
    pm2.01d.1 $e |- ( ph -> ( ps -> -. ps ) ) $.
    $( Deduction based on reductio ad absurdum.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm2.01d $p |- ( ph -> -. ps ) $=
      ( wn wi pm2.01 syl ) ABBDZEHCBFG $.
      $( [31-Jan-2015] $) $( [18-Aug-1993] $)
  $}

  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction from ~ pm2.21 . $)
    pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi pm2.21 syl ) ABEBCFDBCGH $.
      $( [10-Feb-1996] $)
  $}

  $( Theorem *2.24 of [WhiteheadRussell] p. 104. $)
  pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn pm2.21 com12 ) ACABABDE $.
    $( [3-Jan-2005] $)

  ${
    pm2.24d.1 $e |- ( ph -> ps ) $.
    $( Deduction version of ~ pm2.24 .
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm2.24d $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wn wi pm2.24 syl ) ABBECFDBCGH $.
      $( [31-Jan-2015] $) $( [30-Jan-2006] $)
  $}

  ${
    pm2.24i.1 $e |- ph $.
    $( Inference version of ~ pm2.24 .
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm2.24i $p |- ( -. ph -> ps ) $=
      ( wn pm2.21 mpi ) ADABCABEF $.
      $( [31-Jan-2015] $) $( [20-Aug-2001] $)
  $}

  ${
    con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( A contraposition deduction. $)
    con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
      ( wn wi ax-in2 syl6 com23 pm2.01 ) ACBBEZFKABCKABCECKFDCKGHIBJH $.
      $( [12-Feb-2013] $) $( [19-Aug-1993] $)
  $}

  ${
    mt2d.1 $e |- ( ph -> ch ) $.
    mt2d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens deduction. $)
    mt2d $p |- ( ph -> -. ps ) $=
      ( wn con2d mpd ) ACBFDABCEGH $.
      $( [4-Jul-1994] $)
  $}

  ${
    nsyl3.1 $e |- ( ph -> -. ps ) $.
    nsyl3.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference. $)
    nsyl3 $p |- ( ch -> -. ph ) $=
      ( wn wi a1i mt2d ) CABEABFGCDHI $.
      $( [13-Jun-2013] $) $( [1-Dec-1995] $)
  $}

  ${
    con2i.a $e |- ( ph -> -. ps ) $.
    $( A contraposition inference.  (The proof was shortened by O'Cat,
       28-Nov-2008.)  (The proof was shortened by Wolf Lammen, 13-Jun-2013.) $)
    con2i $p |- ( ps -> -. ph ) $=
      ( id nsyl3 ) ABBCBDE $.
      $( [13-Jun-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    nsyl.1 $e |- ( ph -> -. ps ) $.
    nsyl.2 $e |- ( ch -> ps ) $.
    $( A negated syllogism inference.  (The proof was shortened by Wolf Lammen,
       2-Mar-2013.) $)
    nsyl $p |- ( ph -> -. ch ) $=
      ( nsyl3 con2i ) CAABCDEFG $.
      $( [2-Mar-2013] $) $( [31-Dec-1993] $)
  $}

  $( Converse of double negation.  Theorem *2.12 of [WhiteheadRussell] p. 101.
     (The proof was shortened by Wolf Lammen, 2-Mar-2013.) $)
  notnot1 $p |- ( ph -> -. -. ph ) $=
    ( wn id con2i ) ABZAECD $.
    $( [2-Mar-2013] $) $( [5-Aug-1993] $)

  ${
    con3d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A contraposition deduction. $)
    con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $=
      ( wn notnot1 syl6 con2d ) ABCEZABCIEDCFGH $.
      $( [31-Jan-2015] $) $( [5-Aug-1993] $)
  $}

  ${
    con3i.a $e |- ( ph -> ps ) $.
    $( A contraposition inference.  (The proof was shortened by Wolf Lammen,
       20-Jun-2013.) $)
    con3i $p |- ( -. ps -> -. ph ) $=
      ( wn id nsyl ) BDZBAGECF $.
      $( [20-Jun-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    con3rr3.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Rotate through consequent right.  (Contributed by Wolf Lammen,
       3-Nov-2013.) $)
    con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $=
      ( wn con3d com12 ) ACEBEABCDFG $.
      $( [3-Nov-2013] $)
  $}

  $( Theorem *3.2 of [WhiteheadRussell] p. 111, expressed with primitive
     connectives.  (The proof was shortened by Josh Purinton, 29-Dec-2000.) $)
  pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $=
    ( wn wi pm2.27 con2d ) AABCZDBAGEF $.
    $( [5-Aug-1993] $)

  ${
    expi.1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
    $( An exportation inference.  (The proof was shortened by O'Cat,
       28-Nov-2008.) $)
    expi $p |- ( ph -> ( ps -> ch ) ) $=
      ( wn wi pm3.2im syl6 ) ABABEFECABGDH $.
      $( [29-Nov-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    pm2.65i.1 $e |- ( ph -> ps ) $.
    pm2.65i.2 $e |- ( ph -> -. ps ) $.
    $( Inference rule for proof by contradiction.  (The proof was shortened by
       Wolf Lammen, 11-Sep-2013.) $)
    pm2.65i $p |- -. ph $=
      ( wn wi nsyl3 pm2.01 ax-mp ) AAEZFJABADCGAHI $.
      $( [31-Jan-2015] $) $( [18-May-1994] $)
  $}

  ${
    mt2.1 $e |- ps $.
    mt2.2 $e |- ( ph -> -. ps ) $.
    $( A rule similar to modus tollens.  (The proof was shortened by Wolf
       Lammen, 10-Sep-2013.) $)
    mt2 $p |- -. ph $=
      ( a1i pm2.65i ) ABBACEDF $.
      $( [10-Sep-2013] $) $( [19-Aug-1993] $)
  $}

  $( Theorem used to justify definition of biconditional ~ df-bi .  (The proof
     was shortened by Josh Purinton, 29-Dec-2000.) $)
  bijust $p |- -. ( ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                      -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
               -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) )
                      -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) ) $=
    ( wi wn id pm2.01 mt2 ) ABCBACDCDZHCZIDCIHEIFG $.
    $( [18-Nov-2013] $) $( [11-May-1999] $)

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  (The proof
     was shortened by Wolf Lammen, 13-Feb-2013.) $)
  con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi id con3d ) ABCZABFDE $.
    $( [13-Feb-2013] $) $( [5-Aug-1993] $)

  $( Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (The proof
     was shortened by Wolf Lammen, 12-Feb-2013.) $)
  con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $=
    ( wn wi id con2d ) ABCDZABGEF $.
    $( [12-Feb-2013] $) $( [5-Aug-1993] $)

  ${
    mt2i.1 $e |- ch $.
    mt2i.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Modus tollens inference.  (The proof was shortened by Wolf Lammen,
       15-Sep-2012.) $)
    mt2i $p |- ( ph -> -. ps ) $=
      ( a1i mt2d ) ABCCADFEG $.
      $( [15-Sep-2012] $) $( [26-Mar-1995] $)
  $}

  ${
    negbi.1 $e |- ph $.
    $( Infer double negation. $)
    notnoti $p |- -. -. ph $=
      ( wn notnot1 ax-mp ) AACCBADE $.
      $( [27-Feb-2008] $)
  $}

  ${
    pm2.21i.1 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.21 .
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm2.21i $p |- ( ph -> ps ) $=
      ( wn wi pm2.21 ax-mp ) ADABECABFG $.
      $( [31-Jan-2015] $) $( [16-Sep-1993] $)
  $}

  ${
    pm2.24ii.1 $e |- ph $.
    pm2.24ii.2 $e |- -. ph $.
    $( A contradiction implies anything.  Inference from ~ pm2.24 . $)
    pm2.24ii $p |- ps $=
      ( pm2.21i ax-mp ) ABCABDEF $.
      $( [27-Feb-2008] $)
  $}

  ${
    nsyld.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
    nsyld.2 $e |- ( ph -> ( ta -> ch ) ) $.
    $( A negated syllogism deduction. $)
    nsyld $p |- ( ph -> ( ps -> -. ta ) ) $=
      ( wn con3d syld ) ABCGDGEADCFHI $.
      $( [9-Apr-2005] $)
  $}

  ${
    nsyli.1 $e |- ( ph -> ( ps -> ch ) ) $.
    nsyli.2 $e |- ( th -> -. ch ) $.
    $( A negated syllogism inference. $)
    nsyli $p |- ( ph -> ( th -> -. ps ) ) $=
      ( wn con3d syl5 ) DCGABGFABCEHI $.
      $( [3-May-1994] $)
  $}

  $( Theorem 8 of [Margaris] p. 60.  (The proof was shortened by Josh Purinton,
     29-Dec-2000.) $)
  mth8 $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $=
    ( wi pm2.27 con3d ) AABCBABDE $.
    $( [5-Aug-1993] $)

  ${
    jc.1 $e |- ( ph -> ps ) $.
    jc.2 $e |- ( ph -> ch ) $.
    $( Inference joining the consequents of two premises. $)
    jc $p |- ( ph -> -. ( ps -> -. ch ) ) $=
      ( wn wi pm3.2im sylc ) ABCBCFGFDEBCHI $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *2.51 of [WhiteheadRussell] p. 107. $)
  pm2.51 $p |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) ) $=
    ( wi wn ax-1 con3i a1d ) ABCZDBDABHBAEFG $.
    $( [3-Jan-2005] $)

  $( Theorem *2.52 of [WhiteheadRussell] p. 107.
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm2.52 $p |- ( -. ( ph -> ps ) -> ( -. ph -> -. ps ) ) $=
    ( wn wi pm2.21 pm2.24d com12 ) ACZABDZCBCZHIJABEFG $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  $( Exportation theorem expressed with primitive connectives. $)
  expt $p |- ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ) $=
    ( wn wi pm3.2im imim1d com12 ) AABDEDZCEBCEABICABFGH $.
    $( [5-Aug-1993] $)

  $( Elimination of a nested antecedent as a kind of reversal of inference
     ~ ja .  (Contributed by Wolf Lammen, 10-May-2013.) $)
  jarl $p |- ( ( ( ph -> ps ) -> ch ) -> ( -. ph -> ch ) ) $=
    ( wn wi pm2.21 imim1i ) ADABECABFG $.
    $( [10-May-2013] $)

  $( Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction.  (The
     proof was shortened by Wolf Lammen, 8-Mar-2013.) $)
  pm2.65 $p |- ( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) ) $=
    ( wi wn pm2.27 con2d a2i ) ABCAABDZCZABIDAIBAHEFGF $.
    $( [31-Jan-2015] $) $( [5-Aug-1993] $)

  ${
    pm2.65d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.65d.2 $e |- ( ph -> ( ps -> -. ch ) ) $.
    $( Deduction rule for proof by contradiction.  (The proof was shortened by
       Wolf Lammen, 26-May-2013.) $)
    pm2.65d $p |- ( ph -> -. ps ) $=
      ( nsyld pm2.01d ) ABABCBEDFG $.
      $( [26-May-2013] $) $( [26-Jun-1994] $)
  $}

  ${
    pm2.65da.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.65da.2 $e |- ( ( ph /\ ps ) -> -. ch ) $.
    $( Deduction rule for proof by contradiction. $)
    pm2.65da $p |- ( ph -> -. ps ) $=
      ( ex wn pm2.65d ) ABCABCDFABCGEFH $.
      $( [12-Jun-2014] $)
  $}

  ${
    mto.1 $e |- -. ps $.
    mto.2 $e |- ( ph -> ps ) $.
    $( The rule of modus tollens.  (The proof was shortened by Wolf Lammen,
       11-Sep-2013.) $)
    mto $p |- -. ph $=
      ( wn a1i pm2.65i ) ABDBEACFG $.
      $( [11-Sep-2013] $) $( [19-Aug-1993] $)
  $}

  ${
    mtod.1 $e |- ( ph -> -. ch ) $.
    mtod.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens deduction.  (The proof was shortened by Wolf Lammen,
       11-Sep-2013.) $)
    mtod $p |- ( ph -> -. ps ) $=
      ( wn a1d pm2.65d ) ABCEACFBDGH $.
      $( [11-Sep-2013] $) $( [3-Apr-1994] $)
  $}

  ${
    mtoi.1 $e |- -. ch $.
    mtoi.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus tollens inference.  (The proof was shortened by Wolf Lammen,
       15-Sep-2012.) $)
    mtoi $p |- ( ph -> -. ps ) $=
      ( wn a1i mtod ) ABCCFADGEH $.
      $( [15-Sep-2012] $) $( [5-Jul-1994] $)
  $}

  ${
    mtand.1 $e |- ( ph -> -. ch ) $.
    mtand.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( A modus tollens deduction.  (Contributed by Jeff Hankins,
       19-Aug-2009.) $)
    mtand $p |- ( ph -> -. ps ) $=
      ( ex mtod ) ABCDABCEFG $.
      $( [21-Feb-2011] $) $( [15-Jul-2009] $)
  $}

  ${
    notbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction negating both sides of a logical equivalence.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $=
      ( wn biimprd con3d biimpd impbid ) ABECEACBABCDFGABCABCDHGI $.
      $( [31-Jan-2015] $) $( [21-May-1994] $)
  $}

  $( Contraposition.  Bidirectional version of ~ con2 . $)
  con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $=
    ( wn wi con2 impbii ) ABCDBACDABEBAEF $.
    $( [5-Aug-1993] $)

  ${
    notbii.1 $e |- ( ph <-> ps ) $.
    $( Negate both sides of a logical equivalence.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    notbii $p |- ( -. ph <-> -. ps ) $=
      ( wb wn id notbid ax-mp ) ABDZAEBEDCIABIFGH $.
      $( [31-Jan-2015] $) $( [5-Aug-1993] $)
  $}

  ${
    mtbi.1 $e |- -. ph $.
    mtbi.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.  (The proof
       was shortened by Wolf Lammen, 25-Oct-2012.) $)
    mtbi $p |- -. ps $=
      ( biimpri mto ) BACABDEF $.
      $( [25-Oct-2012] $) $( [15-Nov-1994] $)
  $}

  ${
    mtbir.1 $e |- -. ps $.
    mtbir.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.  (The proof
       was shortened by Wolf Lammen, 14-Oct-2012.) $)
    mtbir $p |- -. ph $=
      ( bicomi mtbi ) BACABDEF $.
      $( [13-Oct-2012] $) $( [15-Nov-1994] $)
  $}

  ${
    mtbid.min $e |- ( ph -> -. ps ) $.
    mtbid.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens. $)
    mtbid $p |- ( ph -> -. ch ) $=
      ( biimprd mtod ) ACBDABCEFG $.
      $( [26-Nov-1995] $)
  $}

  ${
    mtbird.min $e |- ( ph -> -. ch ) $.
    mtbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, similar to modus tollens. $)
    mtbird $p |- ( ph -> -. ps ) $=
      ( biimpd mtod ) ABCDABCEFG $.
      $( [10-May-1994] $)
  $}

  ${
    mtbii.min $e |- -. ps $.
    mtbii.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens. $)
    mtbii $p |- ( ph -> -. ch ) $=
      ( biimprd mtoi ) ACBDABCEFG $.
      $( [27-Nov-1995] $)
  $}

  ${
    mtbiri.min $e |- -. ch $.
    mtbiri.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An inference from a biconditional, similar to modus tollens. $)
    mtbiri $p |- ( ph -> -. ps ) $=
      ( biimpd mtoi ) ABCDABCEFG $.
      $( [24-Aug-1995] $)
  $}

  ${
    sylnib.1 $e |- ( ph -> -. ps ) $.
    sylnib.2 $e |- ( ps <-> ch ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnib $p |- ( ph -> -. ch ) $=
      ( wb a1i mtbid ) ABCDBCFAEGH $.
      $( [16-Dec-2013] $)
  $}

  ${
    sylnibr.1 $e |- ( ph -> -. ps ) $.
    sylnibr.2 $e |- ( ch <-> ps ) $.
    $( A mixed syllogism inference from an implication and a biconditional.
       Useful for substituting an consequent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
    sylnibr $p |- ( ph -> -. ch ) $=
      ( bicomi sylnib ) ABCDCBEFG $.
      $( [16-Dec-2013] $)
  $}

  ${
    sylnbi.1 $e |- ( ph <-> ps ) $.
    sylnbi.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       Useful for substituting an antecedent with a definition.  (Contributed
       by Wolf Lammen, 16-Dec-2013.) $)
    sylnbi $p |- ( -. ph -> ch ) $=
      ( wn notbii sylbi ) AFBFCABDGEH $.
      $( [16-Dec-2013] $)
  $}

  ${
    sylnbir.1 $e |- ( ps <-> ph ) $.
    sylnbir.2 $e |- ( -. ps -> ch ) $.
    $( A mixed syllogism inference from a biconditional and an implication.
       (Contributed by Wolf Lammen, 16-Dec-2013.) $)
    sylnbir $p |- ( -. ph -> ch ) $=
      ( bicomi sylnbi ) ABCBADFEG $.
      $( [16-Dec-2013] $)
  $}

  ${
    xchnxbi.1 $e |- ( -. ph <-> ps ) $.
    xchnxbi.2 $e |- ( ph <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbi $p |- ( -. ch <-> ps ) $=
      ( wn notbii bitr3i ) CFAFBACEGDH $.
      $( [27-Sep-2014] $)
  $}

  ${
    xchnxbir.1 $e |- ( -. ph <-> ps ) $.
    xchnxbir.2 $e |- ( ch <-> ph ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchnxbir $p |- ( -. ch <-> ps ) $=
      ( bicomi xchnxbi ) ABCDCAEFG $.
      $( [27-Sep-2014] $)
  $}

  ${
    xchbinx.1 $e |- ( ph <-> -. ps ) $.
    xchbinx.2 $e |- ( ps <-> ch ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinx $p |- ( ph <-> -. ch ) $=
      ( wn notbii bitri ) ABFCFDBCEGH $.
      $( [27-Sep-2014] $)
  $}

  ${
    xchbinxr.1 $e |- ( ph <-> -. ps ) $.
    xchbinxr.2 $e |- ( ch <-> ps ) $.
    $( Replacement of a subexpression by an equivalent one.  (Contributed by
       Wolf Lammen, 27-Sep-2014.) $)
    xchbinxr $p |- ( ph <-> -. ch ) $=
      ( bicomi xchbinx ) ABCDCBEFG $.
      $( [27-Sep-2014] $)
  $}

  ${
    mt2bi.1 $e |- ph $.
    $( A false consequent falsifies an antecedent.  (The proof was shortened by
       Wolf Lammen, 12-Nov-2012.) $)
    mt2bi $p |- ( -. ps <-> ( ps -> -. ph ) ) $=
      ( wn wi a1bi con2b bitri ) BDZAIEBADEAICFABGH $.
      $( [12-Nov-2012] $) $( [19-Aug-1993] $)
  $}

  $( Modus-tollens-like theorem.
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  mtt $p |- ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ) $=
    ( wn wi pm2.21 con3 com12 impbid2 ) ACZBCZBADZBAEKIJBAFGH $.
    $( [31-Jan-2015] $) $( [7-Apr-2001] $)

  $( Two propositions are equivalent if they are both false.  Theorem *5.21 of
     [WhiteheadRussell] p. 124.
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm5.21 $p |- ( ( -. ph /\ -. ps ) -> ( ph <-> ps ) ) $=
    ( wn wa simpl pm2.21d simpr impbid ) ACZBCZDZABKABIJEFKBAIJGFH $.
    $( [31-Jan-2015] $) $( [21-May-1994] $)

  $( Two propositions are equivalent if they are both false.  Closed form of
     ~ 2false .  Equivalent to a ~ bi2 -like version of the xor-connective.
     (Contributed by Wolf Lammen, 13-May-2013.)
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm5.21im $p |- ( -. ph -> ( -. ps -> ( ph <-> ps ) ) ) $=
    ( wn wb pm5.21 ex ) ACBCABDABEF $.
    $( [31-Jan-2015] $) $( [13-May-2013] $)

  $( The negation of a wff is equivalent to the wff's equivalence to
     falsehood.  (Contributed by Juha Arpiainen, 19-Jan-2006.)
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  nbn2 $p |- ( -. ph -> ( -. ps <-> ( ph <-> ps ) ) ) $=
    ( wn wb pm5.21im wi bi2 mtt syl5ibr impbid ) ACZBCZABDZABEMLKBAFABGABHIJ $.
    $( [31-Jan-2015] $) $( [19-Jan-2006] $)

  $( Transfer negation via an equivalence.  (The proof was shortened by Wolf
     Lammen, 28-Jan-2013.) $)
  bibif $p |- ( -. ps -> ( ( ph <-> ps ) <-> -. ph ) ) $=
    ( wn wb nbn2 bicom syl6rbb ) BCACBADABDBAEBAFG $.
    $( [28-Jan-2013] $) $( [3-Oct-2007] $)

  ${
    nbn.1 $e |- -. ph $.
    $( The negation of a wff is equivalent to the wff's equivalence to
       falsehood.  (The proof was shortened by Wolf Lammen, 3-Oct-2013.) $)
    nbn $p |- ( -. ps <-> ( ps <-> ph ) ) $=
      ( wb wn bibif ax-mp bicomi ) BADZBEZAEIJDCBAFGH $.
      $( [3-Oct-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    nbn3.1 $e |- ph $.
    $( Transfer falsehood via equivalence. $)
    nbn3 $p |- ( -. ps <-> ( ps <-> -. ph ) ) $=
      ( wn notnoti nbn ) ADBACEF $.
      $( [11-Sep-2006] $)
  $}

  ${
    2false.1 $e |- -. ph $.
    2false.2 $e |- -. ps $.
    $( Two falsehoods are equivalent.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    2false $p |- ( ph <-> ps ) $=
      ( pm2.21i impbii ) ABABCEBADEF $.
      $( [31-Jan-2015] $) $( [4-Apr-2005] $)
  $}

  ${
    2falsed.1 $e |- ( ph -> -. ps ) $.
    2falsed.2 $e |- ( ph -> -. ch ) $.
    $( Two falsehoods are equivalent (deduction rule). $)
    2falsed $p |- ( ph -> ( ps <-> ch ) ) $=
      ( pm2.21d impbid ) ABCABCDFACBEFG $.
      $( [11-Oct-2013] $)
  $}

  ${
    pm5.21ni.1 $e |- ( ph -> ps ) $.
    pm5.21ni.2 $e |- ( ch -> ps ) $.
    $( Two propositions implying a false one are equivalent.  (The proof was
       shortened by Wolf Lammen, 19-May-2013.) $)
    pm5.21ni $p |- ( -. ps -> ( ph <-> ch ) ) $=
      ( wn con3i 2falsed ) BFACABDGCBEGH $.
      $( [19-May-2013] $) $( [16-Feb-1996] $)

    pm5.21nii.3 $e |- ( ps -> ( ph <-> ch ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm5.21nii $p |- ( ph <-> ch ) $=
      ( wb syl ibi ibir impbii ) ACACABACGZDFHICACBLEFHJK $.
      $( [31-Jan-2015] $) $( [21-May-1999] $)
  $}

  ${
    pm5.21ndd.1 $e |- ( ph -> ( ch -> ps ) ) $.
    pm5.21ndd.2 $e |- ( ph -> ( th -> ps ) ) $.
    pm5.21ndd.3 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional,
       deduction version.  (Contributed by Paul Chapman, 21-Nov-2012.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    pm5.21ndd $p |- ( ph -> ( ch <-> th ) ) $=
      ( wb syld ibd bicom1 syl6 impbid ) ACDACDACBCDHZEGIJADCADNDCHADBNFGICDKLJ
      M $.
      $( [31-Jan-2015] $) $( [21-Nov-2012] $)
  $}

  $( Theorem *5.19 of [WhiteheadRussell] p. 124.
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm5.19 $p |- -. ( ph <-> -. ph ) $=
    ( wn wb bi1 pm2.01d id mpbird pm2.65i ) AABZCZAJAIJAAIDEZJFGKH $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  $( Theorem *4.8 of [WhiteheadRussell] p. 122. $)
  pm4.8 $p |- ( ( ph -> -. ph ) <-> -. ph ) $=
    ( wn wi pm2.01 ax-1 impbii ) AABZCGADGAEF $.
    $( [3-Jan-2005] $)

  $( Express implication in terms of conjunction.
     (Revised by Mario Carneiro, 1-Feb-2015.) $)
  imnan $p |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) ) $=
    ( wn wi wa pm3.2im imp con2i pm3.2 con3rr3 impbii ) ABCDZABEZCMLABLCABFGHAB
    MABIJK $.
    $( [1-Feb-2015] $) $( [9-Apr-1994] $)

  $( Theorem to move a conjunct in and out of a negation. $)
  nan $p |- ( ( ph -> -. ( ps /\ ch ) ) <-> ( ( ph /\ ps ) -> -. ch ) ) $=
    ( wa wn wi impexp imnan imbi2i bitr2i ) ABDCEZFABKFZFABCDEZFABKGLMABCHIJ $.
    $( [9-Nov-2003] $)

  $( Law of noncontradiction.  Theorem *3.24 of [WhiteheadRussell] p. 111 (who
     call it the "law of contradiction").
     (Revised by Mario Carneiro, 2-Feb-2015.) $)
  pm3.24 $p |- -. ( ph /\ -. ph ) $=
    ( wn wi wa notnot1 imnan mpbi ) AABZBCAHDBAEAHFG $.
    $( [2-Feb-2015] $) $( [16-Sep-1993] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical disjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the connective for disjunction ('or'). $)
  $c \/ $. $( Vee (read:  'or') $)

  $( Extend wff definition to include disjunction ('or'). $)
  wo $a wff ( ph \/ ps ) $.

  $( Definition of 'or'.  Axiom 6 of 10 for intuitionistic logic. $)
  ax-io $a |- ( ( ( ph \/ ch ) -> ps ) <->
    ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $.

  $( Disjunction of antecedents.  Compare Theorem *4.77 of [WhiteheadRussell]
     p. 121.  (Revised by Mario Carneiro, 31-Jan-2015.) $)
  jaob $p |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $=
    ( ax-io ) ABCD $.
    $( [31-Jan-2015] $) $( [30-May-1994] $)

  $( Introduction of a disjunct.  Axiom *1.3 of [WhiteheadRussell] p. 96. $)
  olc $p |- ( ph -> ( ps \/ ph ) ) $=
    ( wo wi wa id jaob mpbi simpri ) BBACZDZAJDZJJDKLEJFBJAGHI $.
    $( [31-Jan-2015] $) $( [30-Aug-1993] $)

  $( Introduction of a disjunct.  Theorem *2.2 of [WhiteheadRussell] p. 104. $)
  orc $p |- ( ph -> ( ph \/ ps ) ) $=
    ( wo wi wa id jaob mpbi simpli ) AABCZDZBJDZJJDKLEJFAJBGHI $.
    $( [31-Jan-2015] $) $( [30-Aug-1993] $)

  $( Slight generalization of Theorem *2.67 of [WhiteheadRussell] p. 107. $)
  pm2.67-2 $p |- ( ( ( ph \/ ch ) -> ps ) -> ( ph -> ps ) ) $=
    ( wo orc imim1i ) AACDBACEF $.
    $( [9-Dec-2012] $) $( [3-Jan-2005] $)

  $( Theorem *3.44 of [WhiteheadRussell] p. 113.  (The proof was shortened by
     Wolf Lammen, 3-Oct-2013.) $)
  pm3.44 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) ->
                ( ( ps \/ ch ) -> ph ) ) $=
    ( wo wi wa jaob biimpri ) BCDAEBAECAEFBACGH $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  ${
    jaoi.1 $e |- ( ph -> ps ) $.
    jaoi.2 $e |- ( ch -> ps ) $.
    $( Inference disjoining the antecedents of two implications. $)
    jaoi $p |- ( ( ph \/ ch ) -> ps ) $=
      ( wi wo pm3.44 mp2an ) ABFCBFACGBFDEBACHI $.
      $( [31-Jan-2015] $) $( [5-Apr-1994] $)
  $}

  ${
    jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    $( Deduction disjoining the antecedents of two implications. $)
    jaod $p |- ( ph -> ( ( ps \/ th ) -> ch ) ) $=
      ( wo wi com12 jaoi ) BDGACBACHDABCEIADCFIJI $.
      $( [4-Apr-2013] $) $( [18-Aug-1994] $)
  $}

  ${
    jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of two
       implications. $)
    jaao $p |- ( ( ph /\ th ) -> ( ( ps \/ ta ) -> ch ) ) $=
      ( wa wi adantr adantl jaod ) ADHBCEABCIDFJDECIAGKL $.
      $( [30-Sep-1999] $)

    $( Inference disjoining and conjoining the antecedents of two
       implications.  (Contributed by Stefan Allan, 1-Nov-2008.) $)
    jaoa $p |- ( ( ph \/ th ) -> ( ( ps /\ ta ) -> ch ) ) $=
      ( wa wi adantrd adantld jaoi ) ABEHCIDABCEFJDECBGKL $.
      $( [1-Nov-2008] $)
  $}

  $( Theorem *2.53 of [WhiteheadRussell] p. 107. $)
  pm2.53 $p |- ( ( ph \/ ps ) -> ( -. ph -> ps ) ) $=
    ( wn wi pm2.24 ax-1 jaoi ) AACZBDBABEBHFG $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  ${
    ori.1 $e |- ( ph \/ ps ) $.
    $( Infer implication from disjunction.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    ori $p |- ( -. ph -> ps ) $=
      ( wo wn wi pm2.53 ax-mp ) ABDAEBFCABGH $.
      $( [31-Jan-2015] $) $( [11-Jun-1994] $)
  $}

  ${
    ord.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Deduce implication from disjunction.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    ord $p |- ( ph -> ( -. ps -> ch ) ) $=
      ( wo wn wi pm2.53 syl ) ABCEBFCGDBCHI $.
      $( [31-Jan-2015] $) $( [18-May-1994] $)
  $}

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.55 of
     [WhiteheadRussell] p. 107.  (The proof was shortened by Wolf Lammen,
     21-Jul-2012.) $)
  orel1 $p |- ( -. ph -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wo wn pm2.53 com12 ) ABCADBABEF $.
    $( [23-Jul-2012] $) $( [12-Aug-1994] $)

  $( Elimination of disjunction by denial of a disjunct.  Theorem *2.56 of
     [WhiteheadRussell] p. 107.  (The proof was shortened by Wolf Lammen,
     5-Apr-2013.) $)
  orel2 $p |- ( -. ph -> ( ( ps \/ ph ) -> ps ) ) $=
    ( wn idd pm2.21 jaod ) ACZBBAGBDABEF $.
    $( [5-Apr-2013] $) $( [12-Aug-1994] $)

  $( Axiom *1.4 of [WhiteheadRussell] p. 96. $)
  pm1.4 $p |- ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
    ( wo olc orc jaoi ) ABACBABDBAEF $.
    $( [15-Nov-2012] $) $( [3-Jan-2005] $)

  $( Commutative law for disjunction.  Theorem *4.31 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Wolf Lammen, 15-Nov-2012.) $)
  orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $=
    ( wo pm1.4 impbii ) ABCBACABDBADE $.
    $( [15-Nov-2012] $) $( [5-Aug-1993] $)

  ${
    orcomd.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Commutation of disjuncts in consequent. $)
    orcomd $p |- ( ph -> ( ch \/ ps ) ) $=
      ( wo orcom sylib ) ABCECBEDBCFG $.
      $( [2-Dec-2010] $)
  $}

  ${
    orcoms.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Commutation of disjuncts in antecedent. $)
    orcoms $p |- ( ( ps \/ ph ) -> ch ) $=
      ( wo pm1.4 syl ) BAEABECBAFDG $.
      $( [2-Dec-2012] $)
  $}

  ${
    orci.1 $e |- ph $.
    $( Deduction introducing a disjunct.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    orci $p |- ( ph \/ ps ) $=
      ( wo orc ax-mp ) AABDCABEF $.
      $( [31-Jan-2015] $) $( [19-Jan-2008] $)

    $( Deduction introducing a disjunct.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    olci $p |- ( ps \/ ph ) $=
      ( wo olc ax-mp ) ABADCABEF $.
      $( [31-Jan-2015] $) $( [19-Jan-2008] $)
  $}

  ${
    orcd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing a disjunct. $)
    orcd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wo orc syl ) ABBCEDBCFG $.
      $( [20-Sep-2007] $)

    $( Deduction introducing a disjunct.  (The proof was shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    olcd $p |- ( ph -> ( ch \/ ps ) ) $=
      ( orcd orcomd ) ABCABCDEF $.
      $( [3-Oct-2013] $) $( [11-Apr-2008] $)
  $}

  ${
    orcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct. _Notational convention_:  We sometimes
       suffix with "s" the label of an inference that manipulates an
       antecedent, leaving the consequent unchanged.  The "s" means that the
       inference eliminates the need for a syllogism ( ~ syl ) -type inference
       in a proof. $)
    orcs $p |- ( ph -> ch ) $=
      ( wo orc syl ) AABECABFDG $.
      $( [21-Jun-1994] $)
  $}

  ${
    olcs.1 $e |- ( ( ph \/ ps ) -> ch ) $.
    $( Deduction eliminating disjunct.  (The proof was shortened by Wolf
       Lammen, 3-Oct-2013.) $)
    olcs $p |- ( ps -> ch ) $=
      ( orcoms orcs ) BACABCDEF $.
      $( [3-Oct-2013] $) $( [21-Jun-1994] $)
  $}

  $( Theorem *2.07 of [WhiteheadRussell] p. 101. $)
  pm2.07 $p |- ( ph -> ( ph \/ ph ) ) $=
    ( olc ) AAB $.
    $( [3-Jan-2005] $)

  $( Theorem *2.45 of [WhiteheadRussell] p. 106. $)
  pm2.45 $p |- ( -. ( ph \/ ps ) -> -. ph ) $=
    ( wo orc con3i ) AABCABDE $.
    $( [3-Jan-2005] $)

  $( Theorem *2.46 of [WhiteheadRussell] p. 106. $)
  pm2.46 $p |- ( -. ( ph \/ ps ) -> -. ps ) $=
    ( wo olc con3i ) BABCBADE $.
    $( [3-Jan-2005] $)

  $( Theorem *2.47 of [WhiteheadRussell] p. 107. $)
  pm2.47 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ ps ) ) $=
    ( wo wn pm2.45 orcd ) ABCDADBABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.48 of [WhiteheadRussell] p. 107. $)
  pm2.48 $p |- ( -. ( ph \/ ps ) -> ( ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDAABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.49 of [WhiteheadRussell] p. 107. $)
  pm2.49 $p |- ( -. ( ph \/ ps ) -> ( -. ph \/ -. ps ) ) $=
    ( wo wn pm2.46 olcd ) ABCDBDADABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.67 of [WhiteheadRussell] p. 107. $)
  pm2.67 $p |- ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) ) $=
    ( pm2.67-2 ) ABBC $.
    $( [9-Dec-2012] $) $( [3-Jan-2005] $)

  $( A wff is equivalent to its disjunction with falsehood.  Theorem *4.74 of
     [WhiteheadRussell] p. 121.  (The proof was shortened by Wolf Lammen,
     18-Nov-2012.) $)
  biorf $p |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wn wo olc orel1 impbid2 ) ACBABDBAEABFG $.
    $( [18-Nov-2012] $) $( [23-Mar-1995] $)

  $( A wff is equivalent to its negated disjunction with falsehood. $)
  biortn $p |- ( ph -> ( ps <-> ( -. ph \/ ps ) ) ) $=
    ( wn wo wb notnot1 biorf syl ) AACZCBIBDEAFIBGH $.
    $( [9-Jul-2012] $)

  ${
    biorfi.1 $e |- -. ph $.
    $( A wff is equivalent to its disjunction with falsehood. $)
    biorfi $p |- ( ps <-> ( ps \/ ph ) ) $=
      ( wn wo wb orc orel2 impbid2 ax-mp ) ADZBBAEZFCKBLBAGABHIJ $.
      $( [23-Mar-1995] $)
  $}

  $( Theorem *2.621 of [WhiteheadRussell] p. 107. $)
  pm2.621 $p |- ( ( ph -> ps ) -> ( ( ph \/ ps ) -> ps ) ) $=
    ( wi id idd jaod ) ABCZABBGDGBEF $.
    $( [13-Dec-2013] $) $( [3-Jan-2005] $)

  $( Theorem *2.62 of [WhiteheadRussell] p. 107.  (The proof was shortened by
     Wolf Lammen, 13-Dec-2013.) $)
  pm2.62 $p |- ( ( ph \/ ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi wo pm2.621 com12 ) ABCABDBABEF $.
    $( [13-Dec-2013] $) $( [3-Jan-2005] $)

  ${
    imorri.1 $e |- ( -. ph \/ ps ) $.
    $( Infer implication from disjunction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    imorri $p |- ( ph -> ps ) $=
      ( wn wo wi pm2.21 ax-1 jaoi ax-mp ) ADZBEABFZCKLBABGBAHIJ $.
    $( [31-Jan-2015] $) $( [3-Jun-2011] $)
  $}

  $( Negated disjunction in terms of conjunction (DeMorgan's law).  Compare
     Theorem *4.56 of [WhiteheadRussell] p. 120.
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  ioran $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wo wn wa pm2.45 pm2.46 jca simpl con2i simpr jaoi impbii ) ABCZDZADZBDZEZ
    OPQABFABGHNRARDBRAPQIJRBPQKJLJM $.
    $( [31-Jan-2015] $) $( [5-Aug-1993] $)

  $( Theorem *3.14 of [WhiteheadRussell] p. 111.
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm3.14 $p |- ( ( -. ph \/ -. ps ) -> -. ( ph /\ ps ) ) $=
    ( wn wa simpl con3i simpr jaoi ) ACABDZCBCIAABEFIBABGFH $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  $( Theorem *3.1 of [WhiteheadRussell] p. 111.
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm3.1 $p |- ( ( ph /\ ps ) -> -. ( -. ph \/ -. ps ) ) $=
    ( wn wo wa pm3.14 con2i ) ACBCDABEABFG $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  $( Disjunction of antecedents.  Compare Theorem *3.44 of [WhiteheadRussell]
     p. 113.  (The proof was shortened by Wolf Lammen, 4-Apr-2013.) $)
  jao $p |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( ph \/ ch ) -> ps ) ) ) $=
    ( wi wo pm3.44 ex ) ABDCBDACEBDBACFG $.
    $( [4-Apr-2013] $) $( [5-Apr-1994] $)

  $( Axiom *1.2 (Taut) of [WhiteheadRussell] p. 96. $)
  pm1.2 $p |- ( ( ph \/ ph ) -> ph ) $=
    ( id jaoi ) AAAABZDC $.
    $( [10-Mar-2013] $) $( [3-Jan-2005] $)

  $( Idempotent law for disjunction.  Theorem *4.25 of [WhiteheadRussell]
     p. 117.  (The proof was shortened by Andrew Salmon, 16-Apr-2011.)  (The
     proof was shortened by Wolf Lammen, 10-Mar-2013.) $)
  oridm $p |- ( ( ph \/ ph ) <-> ph ) $=
    ( wo pm1.2 pm2.07 impbii ) AABAACADE $.
    $( [10-Mar-2013] $) $( [5-Aug-1993] $)

  $( Theorem *4.25 of [WhiteheadRussell] p. 117. $)
  pm4.25 $p |- ( ph <-> ( ph \/ ph ) ) $=
    ( wo oridm bicomi ) AABAACD $.
    $( [3-Jan-2005] $)

  ${
    orim12i.1 $e |- ( ph -> ps ) $.
    orim12i.2 $e |- ( ch -> th ) $.
    $( Disjoin antecedents and consequents of two premises.  (The proof was
       shortened by Wolf Lammen, 25-Jul-2012.) $)
    orim12i $p |- ( ( ph \/ ch ) -> ( ps \/ th ) ) $=
      ( wo orcd olcd jaoi ) ABDGCABDEHCDBFIJ $.
      $( [25-Jul-2012] $) $( [6-Jun-1994] $)
  $}

  ${
    orim1i.1 $e |- ( ph -> ps ) $.
    $( Introduce disjunct to both sides of an implication. $)
    orim1i $p |- ( ( ph \/ ch ) -> ( ps \/ ch ) ) $=
      ( id orim12i ) ABCCDCEF $.
      $( [6-Jun-1994] $)

    $( Introduce disjunct to both sides of an implication. $)
    orim2i $p |- ( ( ch \/ ph ) -> ( ch \/ ps ) ) $=
      ( id orim12i ) CCABCEDF $.
      $( [6-Jun-1994] $)
  $}

  ${
    orbi2i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding a left disjunct to both sides of a logical
       equivalence.  (The proof was shortened by Wolf Lammen, 12-Dec-2012.) $)
    orbi2i $p |- ( ( ch \/ ph ) <-> ( ch \/ ps ) ) $=
      ( wo biimpi orim2i biimpri impbii ) CAECBEABCABDFGBACABDHGI $.
      $( [12-Dec-2012] $) $( [5-Aug-1993] $)

    $( Inference adding a right disjunct to both sides of a logical
       equivalence. $)
    orbi1i $p |- ( ( ph \/ ch ) <-> ( ps \/ ch ) ) $=
      ( wo orcom orbi2i 3bitri ) ACECAECBEBCEACFABCDGCBFH $.
      $( [5-Aug-1993] $)
  $}

  ${
    orbi12i.1 $e |- ( ph <-> ps ) $.
    orbi12i.2 $e |- ( ch <-> th ) $.
    $( Infer the disjunction of two equivalences. $)
    orbi12i $p |- ( ( ph \/ ch ) <-> ( ps \/ th ) ) $=
      ( wo orbi2i orbi1i bitri ) ACGADGBDGCDAFHABDEIJ $.
      $( [5-Aug-1993] $)
  $}

  $( Axiom *1.5 (Assoc) of [WhiteheadRussell] p. 96. $)
  pm1.5 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wo orc olcd olc orim2i jaoi ) ABACDZDBCDAJBACEFCJBCAGHI $.
    $( [3-Jan-2005] $)

  $( Swap two disjuncts.  (The proof was shortened by Wolf Lammen,
     14-Nov-2012.) $)
  or12 $p |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) ) $=
    ( wo pm1.5 impbii ) ABCDDBACDDABCEBACEF $.
    $( [14-Nov-2012] $) $( [5-Aug-1993] $)

  $( Associative law for disjunction.  Theorem *4.33 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Andrew Salmon, 26-Jun-2011.) $)
  orass $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo orcom or12 orbi2i 3bitri ) ABDZCDCIDACBDZDABCDZDICECABFJKACBEGH $.
    $( [26-Jun-2011] $) $( [5-Aug-1993] $)

  $( Theorem *2.31 of [WhiteheadRussell] p. 104. $)
  pm2.31 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) ) $=
    ( wo orass biimpri ) ABDCDABCDDABCEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.32 of [WhiteheadRussell] p. 105. $)
  pm2.32 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) ) ) $=
    ( wo orass biimpi ) ABDCDABCDDABCEF $.
    $( [3-Jan-2005] $)

  $( A rearrangement of disjuncts.  (The proof was shortened by Andrew Salmon,
     26-Jun-2011.) $)
  or32 $p |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) ) $=
    ( wo orass or12 orcom 3bitri ) ABDCDABCDDBACDZDIBDABCEABCFBIGH $.
    $( [26-Jun-2011] $) $( [18-Oct-1995] $)

  $( Rearrangement of 4 disjuncts. $)
  or4 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                ( ( ph \/ ch ) \/ ( ps \/ th ) ) ) $=
    ( wo or12 orbi2i orass 3bitr4i ) ABCDEZEZEACBDEZEZEABEJEACELEKMABCDFGABJHAC
    LHI $.
    $( [12-Aug-1994] $)

  $( Rearrangement of 4 disjuncts. $)
  or42 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <->
                 ( ( ph \/ ch ) \/ ( th \/ ps ) ) ) $=
    ( wo or4 orcom orbi2i bitri ) ABECDEEACEZBDEZEJDBEZEABCDFKLJBDGHI $.
    $( [10-Jan-2005] $)

  $( Distribution of disjunction over disjunction. $)
  orordi $p |- ( ( ph \/ ( ps \/ ch ) ) <->
               ( ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $=
    ( wo oridm orbi1i or4 bitr3i ) ABCDZDAADZIDABDACDDJAIAEFAABCGH $.
    $( [25-Feb-1995] $)

  $( Distribution of disjunction over disjunction. $)
  orordir $p |- ( ( ( ph \/ ps ) \/ ch ) <->
               ( ( ph \/ ch ) \/ ( ps \/ ch ) ) ) $=
    ( wo oridm orbi2i or4 bitr3i ) ABDZCDICCDZDACDBCDDJCICEFABCCGH $.
    $( [25-Feb-1995] $)

  $( Theorem *2.3 of [WhiteheadRussell] p. 104. $)
  pm2.3 $p |- ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) ) $=
    ( wo pm1.4 orim2i ) BCDCBDABCEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.41 of [WhiteheadRussell] p. 106. $)
  pm2.41 $p |- ( ( ps \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo olc id jaoi ) BABCZGBADGEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.42 of [WhiteheadRussell] p. 106. $)
  pm2.42 $p |- ( ( -. ph \/ ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wn wi pm2.21 id jaoi ) ACABDZHABEHFG $.
    $( [3-Jan-2005] $)

  $( Theorem *2.4 of [WhiteheadRussell] p. 106. $)
  pm2.4 $p |- ( ( ph \/ ( ph \/ ps ) ) -> ( ph \/ ps ) ) $=
    ( wo orc id jaoi ) AABCZGABDGEF $.
    $( [3-Jan-2005] $)

  $( Theorem *4.44 of [WhiteheadRussell] p. 119. $)
  pm4.44 $p |- ( ph <-> ( ph \/ ( ph /\ ps ) ) ) $=
    ( wa wo orc id simpl jaoi impbii ) AAABCZDAJEAAJAFABGHI $.
    $( [3-Jan-2005] $)

  ${
    mtord.1 $e |- ( ph -> -. ch ) $.
    mtord.2 $e |- ( ph -> -. th ) $.
    mtord.3 $e |- ( ph -> ( ps -> ( ch \/ th ) ) ) $.
    $( A modus tollens deduction involving disjunction.  (Contributed by Jeff
       Hankins, 15-Jul-2009.)
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    mtord $p |- ( ph -> -. ps ) $=
      ( wo wn pm2.21d jaod syld pm2.01d ) ABABCDHBIZGACNDACNEJADNFJKLM $.
      $( [31-Jan-2015] $) $( [15-Jul-2009] $)
  $}

  $( Theorem *4.45 of [WhiteheadRussell] p. 119. $)
  pm4.45 $p |- ( ph <-> ( ph /\ ( ph \/ ps ) ) ) $=
    ( wo orc pm4.71i ) AABCABDE $.
    $( [3-Jan-2005] $)

  $( Theorem *3.48 of [WhiteheadRussell] p. 114. $)
  pm3.48 $p |- ( ( ( ph -> ps ) /\ ( ch -> th ) ) ->
               ( ( ph \/ ch ) -> ( ps \/ th ) ) ) $=
    ( wi wo orc imim2i olc jaao ) ABEABDFZCDECBKABDGHDKCDBIHJ $.
    $( [1-Dec-2012] $) $( [28-Jan-1997] $)

  ${
    orim12d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    orim12d.2 $e |- ( ph -> ( th -> ta ) ) $.
    $( Disjoin antecedents and consequents in a deduction. $)
    orim12d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ ta ) ) ) $=
      ( wi wo pm3.48 syl2anc ) ABCHDEHBDICEIHFGBCDEJK $.
      $( [10-May-1994] $)
  $}

  ${
    orim1d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Disjoin antecedents and consequents in a deduction. $)
    orim1d $p |- ( ph -> ( ( ps \/ th ) -> ( ch \/ th ) ) ) $=
      ( idd orim12d ) ABCDDEADFG $.
      $( [23-Apr-1995] $)

    $( Disjoin antecedents and consequents in a deduction. $)
    orim2d $p |- ( ph -> ( ( th \/ ps ) -> ( th \/ ch ) ) ) $=
      ( idd orim12d ) ADDBCADFEG $.
      $( [23-Apr-1995] $)
  $}

  $( Axiom *1.6 (Sum) of [WhiteheadRussell] p. 97. $)
  orim2 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wi id orim2d ) BCDZBCAGEF $.
    $( [3-Jan-2005] $)

  ${
    orbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding a left disjunct to both sides of a logical
       equivalence.
       (Revised by Mario Carneiro, 31-Jan-2015.) $)
    orbi2d $p |- ( ph -> ( ( th \/ ps ) <-> ( th \/ ch ) ) ) $=
      ( wo biimpd orim2d biimprd impbid ) ADBFDCFABCDABCEGHACBDABCEIHJ $.
      $( [31-Jan-2015] $) $( [5-Aug-1993] $)

    $( Deduction adding a right disjunct to both sides of a logical
       equivalence. $)
    orbi1d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) ) $=
      ( wo orbi2d orcom 3bitr4g ) ADBFDCFBDFCDFABCDEGBDHCDHI $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *4.37 of [WhiteheadRussell] p. 118. $)
  orbi1 $p |- ( ( ph <-> ps ) -> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) ) $=
    ( wb id orbi1d ) ABDZABCGEF $.
    $( [3-Jan-2005] $)

  ${
    orbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    orbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of
       disjunctions. $)
    orbi12d $p |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ ta ) ) ) $=
      ( wo orbi1d orbi2d bitrd ) ABDHCDHCEHABCDFIADECGJK $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem *5.61 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 30-Jun-2013.) $)
  pm5.61 $p |- ( ( ( ph \/ ps ) /\ -. ps ) <-> ( ph /\ -. ps ) ) $=
    ( wn wo biorf orcom syl6rbb pm5.32ri ) BCZABDZAIABADJBAEBAFGH $.
    $( [30-Jun-2013] $) $( [3-Jan-2005] $)

  ${
    jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    $( Inference disjoining the antecedents of two implications. $)
    jaoian $p |- ( ( ( ph \/ th ) /\ ps ) -> ch ) $=
      ( wo wi ex jaoi imp ) ADGBCABCHDABCEIDBCFIJK $.
      $( [23-Oct-2005] $)
  $}

  ${
    jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    $( Deduction disjoining the antecedents of two implications. $)
    jaodan $p |- ( ( ph /\ ( ps \/ th ) ) -> ch ) $=
      ( wo ex jaod imp ) ABDGCABCDABCEHADCFHIJ $.
      $( [14-Oct-2005] $)
  $}

  $( Theorem *4.77 of [WhiteheadRussell] p. 121. $)
  pm4.77 $p |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) <->
                ( ( ps \/ ch ) -> ph ) ) $=
    ( wo wi wa jaob bicomi ) BCDAEBAECAEFBACGH $.
    $( [3-Jan-2005] $)

  $( Theorem *2.63 of [WhiteheadRussell] p. 107. $)
  pm2.63 $p |- ( ( ph \/ ps ) -> ( ( -. ph \/ ps ) -> ps ) ) $=
    ( wo wn pm2.53 idd jaod ) ABCZADBBABEHBFG $.
    $( [3-Jan-2005] $)

  $( Theorem *2.64 of [WhiteheadRussell] p. 107. $)
  pm2.64 $p |- ( ( ph \/ ps ) -> ( ( ph \/ -. ps ) -> ph ) ) $=
    ( wn wo wi ax-1 orel2 jaoi com12 ) ABCZDABDZAAKAEJAKFBAGHI $.
    $( [3-Jan-2005] $)

  $( Theorem *5.53 of [WhiteheadRussell] p. 125. $)
  pm5.53 $p |- ( ( ( ( ph \/ ps ) \/ ch ) -> th ) <->
                ( ( ( ph -> th ) /\ ( ps -> th ) ) /\ ( ch -> th ) ) ) $=
    ( wo wi wa jaob anbi1i bitri ) ABEZCEDFKDFZCDFZGADFBDFGZMGKDCHLNMADBHIJ $.
    $( [3-Jan-2005] $)

  $( Theorem *2.38 of [WhiteheadRussell] p. 105. $)
  pm2.38 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ch \/ ph ) ) ) $=
    ( wi id orim1d ) BCDZBCAGEF $.
    $( [6-Mar-2008] $)

  $( Theorem *2.36 of [WhiteheadRussell] p. 105. $)
  pm2.36 $p |- ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ( ch \/ ph ) ) ) $=
    ( wo wi pm1.4 pm2.38 syl5 ) ABDBADBCECADABFABCGH $.
    $( [6-Mar-2008] $)

  $( Theorem *2.37 of [WhiteheadRussell] p. 105. $)
  pm2.37 $p |- ( ( ps -> ch ) -> ( ( ps \/ ph ) -> ( ph \/ ch ) ) ) $=
    ( wi wo pm2.38 pm1.4 syl6 ) BCDBAECAEACEABCFCAGH $.
    $( [6-Mar-2008] $)

  $( Theorem *2.73 of [WhiteheadRussell] p. 108. $)
  pm2.73 $p |- ( ( ph -> ps ) -> ( ( ( ph \/ ps ) \/ ch ) ->
                ( ps \/ ch ) ) ) $=
    ( wi wo pm2.621 orim1d ) ABDABEBCABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *2.74 of [WhiteheadRussell] p. 108.
     (The proof was shortened by Mario Carneiro, 31-Jan-2015.) $)
  pm2.74 $p |- ( ( ps -> ph ) -> ( ( ( ph \/ ps ) \/ ch ) ->
                ( ph \/ ch ) ) ) $=
    ( wi wo idd id jaod orim1d ) BADZABEACJAABJAFJGHI $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  $( Theorem *2.76 of [WhiteheadRussell] p. 108.
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm2.76 $p |- ( ( ph \/ ( ps -> ch ) ) ->
                ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wo wi orc a1d orim2 jaoi ) AABDZACDZEBCEAKJACFGABCHI $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  $( Theorem *2.75 of [WhiteheadRussell] p. 108.  (The proof was shortened by
     Wolf Lammen, 4-Jan-2013.) $)
  pm2.75 $p |- ( ( ph \/ ps ) ->
                ( ( ph \/ ( ps -> ch ) ) -> ( ph \/ ch ) ) ) $=
    ( wi wo pm2.76 com12 ) ABCDEABEACEABCFG $.
    $( [4-Jan-2013] $) $( [3-Jan-2005] $)

  $( Theorem *2.8 of [WhiteheadRussell] p. 108.
     (The proof was shortened by Mario Carneiro, 31-Jan-2015.) $)
  pm2.8 $p |- ( ( ph \/ ps ) -> ( ( -. ps \/ ch ) -> ( ph \/ ch ) ) ) $=
    ( wo wn pm1.4 ord orim1d ) ABDZBEACIBAABFGH $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  $( Theorem *2.81 of [WhiteheadRussell] p. 108. $)
  pm2.81 $p |- ( ( ps -> ( ch -> th ) ) -> ( ( ph \/ ps ) ->
                ( ( ph \/ ch ) -> ( ph \/ th ) ) ) ) $=
    ( wi wo orim2 pm2.76 syl6 ) BCDEZEABFAJFACFADFEABJGACDHI $.
    $( [3-Jan-2005] $)

  $( Theorem *2.82 of [WhiteheadRussell] p. 108. $)
  pm2.82 $p |- ( ( ( ph \/ ps ) \/ ch ) -> ( ( ( ph \/ -. ch ) \/ th ) ->
                ( ( ph \/ ps ) \/ th ) ) ) $=
    ( wo wn wi ax-1 pm2.24 orim2d jaoi orim1d ) ABEZCEACFZEZMDMOMGCMOHCNBACBIJK
    L $.
    $( [3-Jan-2005] $)

  ${
    pm3.2ni.1 $e |- -. ph $.
    pm3.2ni.2 $e |- -. ps $.
    $( Infer negated disjunction of negated premises. $)
    pm3.2ni $p |- -. ( ph \/ ps ) $=
      ( wo id pm2.21i jaoi mto ) ABEACAABAFBADGHI $.
      $( [4-Apr-1995] $)
  $}

  $( Absorption of redundant internal disjunct.  Compare Theorem *4.45 of
     [WhiteheadRussell] p. 119.  (The proof was shortened by Wolf Lammen,
     28-Feb-2014.) $)
  orabs $p |- ( ph <-> ( ( ph \/ ps ) /\ ph ) ) $=
    ( wo orc pm4.71ri ) AABCABDE $.
    $( [28-Feb-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ orabs as of 28-Feb-2014. $)
  orabsOLD $p |- ( ph <-> ( ( ph \/ ps ) /\ ph ) ) $=
    ( wo wa orc ancri simpr impbii ) AABCZADAIABEFIAGH $.
    $( [5-Aug-1993] $)

  $( Absorb a disjunct into a conjunct.  (Contributed by Roy F. Longton
     23-Jun-2005.)  (The proof was shortened by Wolf Lammen, 10-Nov-2013.) $)
  oranabs $p |- ( ( ( ph \/ -. ps ) /\ ps ) <-> ( ph /\ ps ) ) $=
    ( wn wo biortn orcom syl6rbb pm5.32ri ) BABCZDZABAIADJBAEIAFGH $.
    $( [10-Nov-2013] $) $( [23-Jun-2005] $)

  $( Distributive law for disjunction.  Theorem *4.41 of [WhiteheadRussell]
     p. 119.  (Revised by Mario Carneiro, 31-Jan-2015.) $)
  ordi $p |- ( ( ph \/ ( ps /\ ch ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) ) $=
    ( wa wo simpl orim2i simpr jca orc adantl adantr olc jaoian jaodan impbii )
    ABCDZEZABEZACEZDRSTQBABCFGQCABCHGISARCARSAQJZKACRBARCUALQAMNOP $.
    $( [31-Jan-2015] $) $( [5-Aug-1993] $)

  $( Distributive law for disjunction. $)
  ordir $p |- ( ( ( ph /\ ps ) \/ ch ) <->
              ( ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    ( wa wo ordi orcom anbi12i 3bitr4i ) CABDZECAEZCBEZDJCEACEZBCEZDCABFJCGMKNL
    ACGBCGHI $.
    $( [12-Aug-1994] $)

  $( Distributive law for conjunction.  Theorem *4.4 of [WhiteheadRussell]
     p. 118.  (The proof was shortened by Wolf Lammen, 5-Jan-2013.) $)
  andi $p |- ( ( ph /\ ( ps \/ ch ) ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) ) ) $=
    ( wo wa orc olc jaodan anim2i jaoi impbii ) ABCDZEZABEZACEZDZABPCNOFONGHNMO
    BLABCFICLACBGIJK $.
    $( [5-Jan-2013] $) $( [5-Aug-1993] $)

  $( Distributive law for conjunction. $)
  andir $p |- ( ( ( ph \/ ps ) /\ ch ) <->
              ( ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $=
    ( wo wa andi ancom orbi12i 3bitr4i ) CABDZECAEZCBEZDJCEACEZBCEZDCABFJCGMKNL
    ACGBCGHI $.
    $( [12-Aug-1994] $)

  $( Double distributive law for disjunction. $)
  orddi $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
              ( ( ( ph \/ ch ) /\ ( ph \/ th ) ) /\
              ( ( ps \/ ch ) /\ ( ps \/ th ) ) ) ) $=
    ( wa wo ordir ordi anbi12i bitri ) ABECDEZFAKFZBKFZEACFADFEZBCFBDFEZEABKGLN
    MOACDHBCDHIJ $.
    $( [12-Aug-1994] $)

  $( Double distributive law for conjunction. $)
  anddi $p |- ( ( ( ph \/ ps ) /\ ( ch \/ th ) ) <->
              ( ( ( ph /\ ch ) \/ ( ph /\ th ) ) \/
              ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) ) $=
    ( wo wa andir andi orbi12i bitri ) ABECDEZFAKFZBKFZEACFADFEZBCFBDFEZEABKGLN
    MOACDHBCDHIJ $.
    $( [12-Aug-1994] $)

  $( Prove formula-building rules for the biconditional connective. $)

  $( Theorem *4.39 of [WhiteheadRussell] p. 118. $)
  pm4.39 $p |- ( ( ( ph <-> ch ) /\ ( ps <-> th ) ) ->
                ( ( ph \/ ps ) <-> ( ch \/ th ) ) ) $=
    ( wb wa simpl simpr orbi12d ) ACEZBDEZFACBDJKGJKHI $.
    $( [3-Jan-2005] $)

  $( Implication in terms of biconditional and disjunction.  Theorem *4.72 of
     [WhiteheadRussell] p. 121.  (The proof was shortened by Wolf Lammen,
     30-Jan-2013.) $)
  pm4.72 $p |- ( ( ph -> ps ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wo wb olc pm2.621 impbid2 orc bi2 syl5 impbii ) ABCZBABDZEZMBNBAFABGHA
    NOBABIBNJKL $.
    $( [30-Jan-2013] $) $( [30-Aug-1993] $)

  $( Theorem *5.16 of [WhiteheadRussell] p. 124.
     (Revised by Mario Carneiro, 31-Jan-2015.) $)
  pm5.16 $p |- -. ( ( ph <-> ps ) /\ ( ph <-> -. ps ) ) $=
    ( wb wn wa pm5.19 simpl simpr bitr3d mto ) ABCZABDZCZEZBLCBFNABLKMGKMHIJ $.
    $( [31-Jan-2015] $) $( [3-Jan-2005] $)

  $( A wff is disjoined with truth is true. $)
  biort $p |- ( ph -> ( ph <-> ( ph \/ ps ) ) ) $=
    ( wo orc ax-1 impbid2 ) AAABCZABDAGEF $.
    $( [23-May-1999] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Classical logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( This section makes our first use of the third axiom of propositonal
   calculus. $)

  ${
    con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Deduction derived from axiom ~ ax-3 . $)
    con4d $p |- ( ph -> ( ch -> ps ) ) $=
      ( wn wi ax-3 syl ) ABECEFCBFDBCGH $.
      $( [26-Mar-1995] $)
  $}

  $( Proof by contradiction.  Theorem *2.18 of [WhiteheadRussell] p. 103.  Also
     called the Law of Clavius. $)
  pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi pm2.21 a2i con4d pm2.43i ) ABZACZAIAIHAIBZAJDEFG $.
    $( [5-Aug-1993] $)

  ${
    pm2.18d.1 $e |- ( ph -> ( -. ps -> ps ) ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by FL,
       12-Jul-2009.)  (The proof was shortened by Andrew Salmon,
       7-May-2011.) $)
    pm2.18d $p |- ( ph -> ps ) $=
      ( wn wi pm2.18 syl ) ABDBEBCBFG $.
      $( [7-May-2011] $) $( [12-Jul-2009] $)
  $}

  $( Converse of double negation.  Theorem *2.14 of [WhiteheadRussell] p. 102.
     (The proof was shortened by David Harvey, 5-Sep-1999.  An even shorter
     proof found by Josh Purinton, 29-Dec-2000.) $)
  notnot2 $p |- ( -. -. ph -> ph ) $=
    ( wn pm2.21 pm2.18d ) ABZBAEACD $.
    $( [5-Aug-1993] $)

  ${
    negai.1 $e |- -. -. ph $.
    $( Inference from double negation. $)
    notnotri $p |- ph $=
      ( wn notnot2 ax-mp ) ACCABADE $.
      $( [27-Feb-2008] $)
  $}

  ${
    con1d.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( A contraposition deduction. $)
    con1d $p |- ( ph -> ( -. ch -> ps ) ) $=
      ( wn notnot1 syl6 con4d ) ABCEZABECIEDCFGH $.
      $( [12-Feb-2013] $) $( [5-Aug-1993] $)
  $}

  $( Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102.  (The proof
     was shortened by Wolf Lammen, 12-Feb-2013.) $)
  con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    ( wn wi id con1d ) ACBDZABGEF $.
    $( [12-Feb-2013] $) $( [5-Aug-1993] $)

  ${
    mt3d.1 $e |- ( ph -> -. ch ) $.
    mt3d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens deduction. $)
    mt3d $p |- ( ph -> ps ) $=
      ( wn con1d mpd ) ACFBDABCEGH $.
      $( [26-Mar-1995] $)
  $}

  ${
    mt3i.1 $e |- -. ch $.
    mt3i.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Modus tollens inference.  (The proof was shortened by Wolf Lammen,
       15-Sep-2012.) $)
    mt3i $p |- ( ph -> ps ) $=
      ( wn a1i mt3d ) ABCCFADGEH $.
      $( [15-Sep-2012] $) $( [26-Mar-1995] $)
  $}

  ${
    mt3.1 $e |- -. ps $.
    mt3.2 $e |- ( -. ph -> ps ) $.
    $( A rule similar to modus tollens.  (The proof was shortened by Wolf
       Lammen, 11-Sep-2013.) $)
    mt3 $p |- ph $=
      ( wn mto notnotri ) AAEBCDFG $.
      $( [11-Sep-2013] $) $( [18-May-1994] $)
  $}

  ${
    nsyl2.1 $e |- ( ph -> -. ps ) $.
    nsyl2.2 $e |- ( -. ch -> ps ) $.
    $( A negated syllogism inference. $)
    nsyl2 $p |- ( ph -> ch ) $=
      ( wn wi a1i mt3d ) ACBDCFBGAEHI $.
      $( [19-Jun-2013] $) $( [26-Jun-1994] $)
  $}

  ${
    con1i.a $e |- ( -. ph -> ps ) $.
    $( A contraposition inference.  (The proof was shortened by O'Cat,
       28-Nov-2008.)  (The proof was shortened by Wolf Lammen, 19-Jun-2013.) $)
    con1i $p |- ( -. ps -> ph ) $=
      ( wn id nsyl2 ) BDZBAGECF $.
      $( [19-Jun-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    nsyl4.1 $e |- ( ph -> ps ) $.
    nsyl4.2 $e |- ( -. ph -> ch ) $.
    $( A negated syllogism inference. $)
    nsyl4 $p |- ( -. ch -> ps ) $=
      ( wn con1i syl ) CFABACEGDH $.
      $( [15-Feb-1996] $)
  $}

  ${
    con4i.1 $e |- ( -. ph -> -. ps ) $.
    $( Inference rule derived from axiom ~ ax-3 .  (The proof was shortened by
       Wolf Lammen, 21-Jun-2013.) $)
    con4i $p |- ( ps -> ph ) $=
      ( wn notnot1 nsyl2 ) BBDABECF $.
      $( [21-Jun-2013] $) $( [5-Aug-1993] $)
  $}

  ${
    impi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( An importation inference.  (The proof was shortened by Wolf Lammen,
       20-Jul-2013.) $)
    impi $p |- ( -. ( ph -> -. ps ) -> ch ) $=
      ( wn wi con3rr3 con1i ) CABEFABCDGH $.
      $( [20-Jul-2013] $) $( [5-Aug-1993] $)
  $}

  $( Simplification.  Similar to Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (The proof was shortened by Wolf Lammen, 13-Nov-2012.) $)
  simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $=
    ( idd impi ) ABBABCD $.
    $( [13-Nov-2012] $) $( [5-Aug-1993] $)

  $( Simplification.  Similar to Theorem *3.26 (Simp) of [WhiteheadRussell]
     p. 112.  (The proof was shortened by Wolf Lammen, 21-Jul-2012.) $)
  simplim $p |- ( -. ( ph -> ps ) -> ph ) $=
    ( wi pm2.21 con1i ) AABCABDE $.
    $( [23-Jul-2012] $) $( [5-Aug-1993] $)

  ${
    mt4.1 $e |- ph $.
    mt4.2 $e |- ( -. ps -> -. ph ) $.
    $( The rule of modus tollens.  (Contributed by Wolf Lammen,
       12-May-2013.) $)
    mt4 $p |- ps $=
      ( con4i ax-mp ) ABCBADEF $.
      $( [12-May-2013] $)
  $}

  ${
    mt4d.1 $e |- ( ph -> ps ) $.
    mt4d.2 $e |- ( ph -> ( -. ch -> -. ps ) ) $.
    $( Modus tollens deduction. $)
    mt4d $p |- ( ph -> ch ) $=
      ( con4d mpd ) ABCDACBEFG $.
      $( [9-Jun-2006] $)
  $}

  ${
    mt4i.1 $e |- ch $.
    mt4i.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( Modus tollens inference.  (Contributed by Wolf Lammen, 12-May-2013.) $)
    mt4i $p |- ( ph -> ps ) $=
      ( a1i mt4d ) ACBCADFEG $.
      $( [10-Sep-2013] $) $( [12-May-2013] $)
  $}

  ${
    pm2.61d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d.2 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduction eliminating an antecedent.  (The proof was shortened by Wolf
       Lammen, 12-Sep-2013.) $)
    pm2.61d $p |- ( ph -> ch ) $=
      ( wn con1d syld pm2.18d ) ACACFBCABCEGDHI $.
      $( [12-Sep-2013] $) $( [27-Apr-1994] $)
  $}

  ${
    pm2.61d1.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61d1.2 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating an antecedent. $)
    pm2.61d1 $p |- ( ph -> ch ) $=
      ( wn wi a1i pm2.61d ) ABCDBFCGAEHI $.
      $( [15-Jul-2005] $)
  $}

  ${
    pm2.61d2.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    pm2.61d2.2 $e |- ( ps -> ch ) $.
    $( Inference eliminating an antecedent. $)
    pm2.61d2 $p |- ( ph -> ch ) $=
      ( wi a1i pm2.61d ) ABCBCFAEGDH $.
      $( [18-Aug-1993] $)
  $}

  ${
    ja.1 $e |- ( -. ph -> ch ) $.
    ja.2 $e |- ( ps -> ch ) $.
    $( Inference joining the antecedents of two premises.  (The proof was
       shortened by O'Cat, 19-Feb-2008.) $)
    ja $p |- ( ( ph -> ps ) -> ch ) $=
      ( wi imim2i pm2.61d1 ) ABFACBCAEGDH $.
      $( [19-Feb-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    jad.1 $e |- ( ph -> ( -. ps -> th ) ) $.
    jad.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction form of ~ ja .  (Contributed by Scott Fenton, 13-Dec-2010.)
       (The proof was shortened by Andrew Salmon, 17-Sep-2011.) $)
    jad $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
      ( wi wn com12 ja ) BCGADBCADGABHDEIACDFIJI $.
      $( [17-Sep-2011] $) $( [13-Dec-2010] $)
  $}

  $( Peirce's axiom.  This odd-looking theorem is the "difference" between an
     intuitionistic system of propositional calculus and a classical system and
     is not accepted by intuitionists.  When Peirce's axiom is added to an
     intuitionistic system, the system becomes equivalent to our classical
     system ~ ax-1 through ~ ax-3 .  A curious fact about this theorem is that
     it requires ~ ax-3 for its proof even though the result has no negation
     connectives in it.  (The proof was shortened by Wolf Lammen,
     9-Oct-2012.) $)
  peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( wi simplim id ja ) ABCAAABDAEF $.
    $( [9-Oct-2012] $) $( [5-Aug-1993] $)

  $( Theorem *2.6 of [WhiteheadRussell] p. 107. $)
  pm2.6 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wn wi id idd jad ) ACBDZABBHEHBFG $.
    $( [22-Sep-2013] $) $( [3-Jan-2005] $)

  $( Theorem *2.61 of [WhiteheadRussell] p. 107.  Useful for eliminating an
     antecedent.  (The proof was shortened by Wolf Lammen, 22-Sep-2013.) $)
  pm2.61 $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $=
    ( wn wi pm2.6 com12 ) ACBDABDBABEF $.
    $( [22-Sep-2013] $) $( [5-Aug-1993] $)

  ${
    pm2.61i.1 $e |- ( ph -> ps ) $.
    pm2.61i.2 $e |- ( -. ph -> ps ) $.
    $( Inference eliminating an antecedent.  (The proof was shortened by Wolf
       Lammen, 12-Sep-2013.) $)
    pm2.61i $p |- ps $=
      ( wi id ja ax-mp ) AAEBAFAABDCGH $.
      $( [12-Sep-2013] $) $( [5-Apr-1994] $)
  $}

  ${
    pm2.61ii.1 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    pm2.61ii.2 $e |- ( ph -> ch ) $.
    pm2.61ii.3 $e |- ( ps -> ch ) $.
    $( Inference eliminating two antecedents.  (The proof was shortened by Josh
       Purinton, 29-Dec-2000.) $)
    pm2.61ii $p |- ch $=
      ( wn pm2.61d2 pm2.61i ) ACEAGBCDFHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    pm2.61ian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61ian.2 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    $( Elimination of an antecedent. $)
    pm2.61ian $p |- ( ps -> ch ) $=
      ( wi ex wn pm2.61i ) ABCFABCDGAHBCEGI $.
      $( [1-Jan-2005] $)
  $}

  ${
    pm2.61dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    pm2.61dan.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    $( Elimination of an antecedent. $)
    pm2.61dan $p |- ( ph -> ch ) $=
      ( ex wn pm2.61d ) ABCABCDFABGCEFH $.
      $( [1-Jan-2005] $)
  $}

  ${
    pm2.61ddan.1 $e |- ( ( ph /\ ps ) -> th ) $.
    pm2.61ddan.2 $e |- ( ( ph /\ ch ) -> th ) $.
    pm2.61ddan.3 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
    $( Elimination of two antecedents. $)
    pm2.61ddan $p |- ( ph -> th ) $=
      ( wn wa adantlr anassrs pm2.61dan ) ABDEABHZICDACDMFJAMCHDGKLL $.
      $( [9-Jul-2013] $)
  $}

  ${
    pm2.61dda.1 $e |- ( ( ph /\ -. ps ) -> th ) $.
    pm2.61dda.2 $e |- ( ( ph /\ -. ch ) -> th ) $.
    pm2.61dda.3 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Elimination of two antecedents. $)
    pm2.61dda $p |- ( ph -> th ) $=
      ( wa anassrs wn adantlr pm2.61dan ) ABDABHCDABCDGIACJDBFKLEL $.
      $( [9-Jul-2013] $)
  $}

  ${
    pm2.61nii.1 $e |- ( ph -> ( ps -> ch ) ) $.
    pm2.61nii.2 $e |- ( -. ph -> ch ) $.
    pm2.61nii.3 $e |- ( -. ps -> ch ) $.
    $( Inference eliminating two antecedents.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.)  (The proof was shortened by Wolf Lammen,
       13-Nov-2012.) $)
    pm2.61nii $p |- ch $=
      ( pm2.61d1 pm2.61i ) ACABCDFGEH $.
      $( [13-Nov-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    pm2.61iii.1 $e |- ( -. ph -> ( -. ps -> ( -. ch -> th ) ) ) $.
    pm2.61iii.2 $e |- ( ph -> th ) $.
    pm2.61iii.3 $e |- ( ps -> th ) $.
    pm2.61iii.4 $e |- ( ch -> th ) $.
    $( Inference eliminating three antecedents.  (The proof was shortened by
       Wolf Lammen, 22-Sep-2013.) $)
    pm2.61iii $p |- th $=
      ( wn wi a1d pm2.61ii pm2.61i ) CDHABCIZDJEADNFKBDNGKLM $.
      $( [22-Sep-2013] $) $( [2-Jan-2002] $)
  $}

  $( Importation theorem expressed with primitive connectives.  (The proof was
     shortened by Wolf Lammen, 20-Jul-2013.) $)
  impt $p |- ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) ) $=
    ( wi wn simprim simplim imim1i mpdi ) ABCDZDABEZDEZBCABFLAJAKGHI $.
    $( [20-Jul-2013] $) $( [25-Apr-1994] $)

  ${
    impcon4bid.1 $e |- ( ph -> ( ps -> ch ) ) $.
    impcon4bid.2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
    $( A variation on ~ impbid with contraposition.  (Contributed by Jeff
       Hankins, 3-Jul-2009.) $)
    impcon4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( con4d impbid ) ABCDABCEFG $.
      $( [3-Jul-2009] $)
  $}

  $( Theorem *2.5 of [WhiteheadRussell] p. 107.  (The proof was shortened by
     Wolf Lammen, 9-Oct-2012.) $)
  pm2.5 $p |- ( -. ( ph -> ps ) -> ( -. ph -> ps ) ) $=
    ( wi wn simplim pm2.24d ) ABCDABABEF $.
    $( [9-Oct-2012] $) $( [3-Jan-2005] $)

  $( Theorem *2.521 of [WhiteheadRussell] p. 107.  (The proof was shortened by
     Wolf Lammen, 8-Oct-2012.) $)
  pm2.521 $p |- ( -. ( ph -> ps ) -> ( ps -> ph ) ) $=
    ( wi wn simplim a1d ) ABCDABABEF $.
    $( [8-Oct-2012] $) $( [3-Jan-2005] $)

  $( The Linearity Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  For a version not using ~ ax-3 , see ~ loolinALT .
     (Contributed by O'Cat, 12-Aug-2004.)  (The proof was shortened by Wolf
     Lammen, 2-Nov-2012.) $)
  loolin $p |- ( ( ( ph -> ps ) -> ( ps -> ph ) ) -> ( ps -> ph ) ) $=
    ( wi pm2.521 id ja ) ABCBACZGABDGEF $.
    $( [2-Nov-2012] $) $( [12-Aug-2004] $)

  $( The Inversion Axiom of the infinite-valued sentential logic (L-infinity)
     of Lukasiewicz.  Using ~ dfor2 , we can see that this essentially
     expresses "disjunction commutes."  Theorem *2.69 of [WhiteheadRussell]
     p. 108. $)
  looinv $p |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    ( wi imim1 peirce syl6 ) ABCZBCBACGACAGBADABEF $.
    $( [12-Aug-2004] $)

  $( Contraposition.  Theorem *4.1 of [WhiteheadRussell] p. 116. $)
  con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $=
    ( wi wn con3 ax-3 impbii ) ABCBDADCABEBAFG $.
    $( [5-Aug-1993] $)

  $( Double negation.  Theorem *4.13 of [WhiteheadRussell] p. 117. $)
  notnot $p |- ( ph <-> -. -. ph ) $=
    ( wn notnot1 notnot2 impbii ) AABBACADE $.
    $( [5-Aug-1993] $)

  ${
    con4bid.1 $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
    $( A contraposition deduction. $)
    con4bid $p |- ( ph -> ( ps <-> ch ) ) $=
      ( wn biimprd con4d biimpd impcon4bid ) ABCACBABEZCEZDFGAJKDHI $.
      $( [17-Sep-2013] $) $( [21-May-1994] $)
  $}

  $( Contraposition.  Theorem *4.11 of [WhiteheadRussell] p. 117.  (The proof
     was shortened by Wolf Lammen, 12-Jun-2013.) $)
  notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $=
    ( wb wn id notbid con4bid impbii ) ABCZADBDCZIABIEFJABJEGH $.
    $( [12-Jun-2013] $) $( [21-May-1994] $)

  $( Contraposition.  Theorem *4.12 of [WhiteheadRussell] p. 117.  (The proof
     was shortened by Wolf Lammen, 3-Jan-2013.) $)
  con2bi $p |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) ) $=
    ( wn wb notbi notnot bibi2i bicom 3bitr2i ) ABCZDACZJCZDKBDBKDAJEBLKBFGKBHI
    $.
    $( [3-Jan-2013] $) $( [15-Apr-1995] $)

  ${
    con2bid.1 $e |- ( ph -> ( ps <-> -. ch ) ) $.
    $( A contraposition deduction. $)
    con2bid $p |- ( ph -> ( ch <-> -. ps ) ) $=
      ( wn wb con2bi sylibr ) ABCEFCBEFDCBGH $.
      $( [15-Apr-1995] $)
  $}

  ${
    con1bid.1 $e |- ( ph -> ( -. ps <-> ch ) ) $.
    $( A contraposition deduction. $)
    con1bid $p |- ( ph -> ( -. ch <-> ps ) ) $=
      ( wn bicomd con2bid ) ABCEACBABECDFGF $.
      $( [9-Oct-1999] $)
  $}

  ${
    con1bii.1 $e |- ( -. ph <-> ps ) $.
    $( A contraposition inference.  (The proof was shortened by Wolf Lammen,
       13-Oct-2012.) $)
    con1bii $p |- ( -. ps <-> ph ) $=
      ( wn notnot xchbinx bicomi ) ABDAADBAECFG $.
      $( [28-Sep-2014] $) $( [5-Aug-1993] $)
  $}

  ${
    con1biiOLD.1 $e |- ( -. ph <-> ps ) $.
    $( Obsolete proof of ~ con1bii as of 28-Sep-2014. $)
    con1biiOLD $p |- ( -. ps <-> ph ) $=
      ( wn notnot notbii bitr2i ) AADZDBDAEHBCFG $.
      $( [13-Oct-2012] $) $( [5-Aug-1993] $)
  $}

  $( Contraposition.  Bidirectional version of ~ con1 . $)
  con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $=
    ( wn wi con1 impbii ) ACBDBCADABEBAEF $.
    $( [5-Aug-1993] $)

  ${
    con4bii.1 $e |- ( -. ph <-> -. ps ) $.
    $( A contraposition inference. $)
    con4bii $p |- ( ph <-> ps ) $=
      ( wb wn notbi mpbir ) ABDAEBEDCABFG $.
      $( [21-May-1994] $)
  $}

  ${
    con2bii.1 $e |- ( ph <-> -. ps ) $.
    $( A contraposition inference. $)
    con2bii $p |- ( ps <-> -. ph ) $=
      ( wn bicomi con1bii ) ADBBAABDCEFE $.
      $( [5-Aug-1993] $)
  $}

  ${
    bija.1 $e |- ( ph -> ( ps -> ch ) ) $.
    bija.2 $e |- ( -. ph -> ( -. ps -> ch ) ) $.
    $( Combine antecedents into a single bi-conditional.  This inference,
       reminiscent of ~ ja , is reversible:  The hypotheses can be deduced from
       the conclusion alone (see ~ pm5.1im and ~ pm5.21im ).  (Contributed by
       Wolf Lammen, 13-May-2013.) $)
    bija $p |- ( ( ph <-> ps ) -> ch ) $=
      ( wb bi2 syli wn bi1 con3d pm2.61d ) ABFZBCBMACABGDHBIMAICMABABJKEHL $.
      $( [13-May-2013] $)
  $}

  $( Theorem *5.18 of [WhiteheadRussell] p. 124.  This theorem says that
     logical equivalence is the same as negated "exclusive-or."  (The proof was
     shortened by Andrew Salmon, 20-Jun-2011.)  (The proof was shortened by
     Wolf Lammen, 15-Oct-2013.) $)
  pm5.18 $p |- ( ( ph <-> ps ) <-> -. ( ph <-> -. ps ) ) $=
    ( wb wn pm5.501 con1bid bitr2d nbn2 pm2.61i ) AABCZABDZCZDZCAMBJABLAKEFABEG
    ADZMKJNKLAKHFABHGI $.
    $( [15-Oct-2013] $) $( [28-Jun-2002] $)

  $( Two ways to express "exclusive or." $)
  xor3 $p |- ( -. ( ph <-> ps ) <-> ( ph <-> -. ps ) ) $=
    ( wn wb pm5.18 con2bii bicomi ) ABCDZABDZCIHABEFG $.
    $( [1-Jan-2006] $)

  $( Move negation outside of biconditional.  Compare Theorem *5.18 of
     [WhiteheadRussell] p. 124.  (The proof was shortened by Wolf Lammen,
     20-Sep-2013.) $)
  nbbn $p |- ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) ) $=
    ( wb wn xor3 con2bi bicom 3bitrri ) ABCDABDCBADZCIBCABEABFBIGH $.
    $( [20-Sep-2013] $) $( [27-Jun-2002] $)

  $( Associative law for the biconditional.  An axiom of system DS in Vladimir
     Lifschitz, "On calculational proofs", Annals of Pure and Applied Logic,
     113:207-224, 2002,
     ~ http://www.cs.utexas.edu/users/ai-lab/pub-view.php?PubID=26805 .
     Interestingly, this law was not included in _Principia Mathematica_ but
     was apparently first noted by Jan Lukasiewicz circa 1923.  (The proof was
     shortened by Juha Arpiainen, 19-Jan-2006.)  (The proof was shortened by
     Wolf Lammen, 21-Sep-2013.) $)
  biass $p |- ( ( ( ph <-> ps ) <-> ch ) <-> ( ph <-> ( ps <-> ch ) ) ) $=
    ( wb pm5.501 bibi1d bitr3d wn nbbn nbn2 syl5bbr pm2.61i ) AABDZCDZABCDZDZDA
    ONPABMCABEFAOEGAHZOHZNPRBHZCDQNBCIQSMCABJFKAOJGL $.
    $( [21-Sep-2013] $) $( [8-Jan-2005] $)

  $( Theorem *4.81 of [WhiteheadRussell] p. 122. $)
  pm4.81 $p |- ( ( -. ph -> ph ) <-> ph ) $=
    ( wn wi pm2.18 pm2.24 impbii ) ABACAADAAEF $.
    $( [3-Jan-2005] $)

  $( Definition of 'and' in terms of negation and implication (classical). $)
  df-an $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
    ( wa wn wi pm3.2im imp simplim simprim jca impbii ) ABCABDZEDZABMABFGMABALH
    ABIJK $.
    $( [31-Jan-2015] $)

  $( Theorem *4.63 of [WhiteheadRussell] p. 120. $)
  pm4.63 $p |- ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ) $=
    ( wa wn wi df-an bicomi ) ABCABDEDABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *4.67 of [WhiteheadRussell] p. 120. $)
  pm4.67 $p |- ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ) $=
    ( wn pm4.63 ) ACBD $.
    $( [3-Jan-2005] $)

  $( Relate the biconditional connective to primitive connectives. $)
  dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wb wi wa wn dfbi2 df-an bitri ) ABCABDZBADZEJKFDFABGJKHI $.
    $( [31-Jan-2015] $) $( [5-Aug-1993] $)

  $( Express implication in terms of conjunction.  Theorem 3.4(27) of [Stoll]
     p. 176.  (The proof was shortened by Wolf Lammen, 30-Oct-2012.) $)
  iman $p |- ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) ) $=
    ( wi wn wa notnot imbi2i imnan bitri ) ABCABDZDZCAJEDBKABFGAJHI $.
    $( [30-Oct-2012] $) $( [5-Aug-1993] $)

  $( Express conjunction in terms of implication. $)
  annim $p |- ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) ) $=
    ( wi wn wa iman con2bii ) ABCABDEABFG $.
    $( [2-Aug-1994] $)

  $( Theorem *4.61 of [WhiteheadRussell] p. 120. $)
  pm4.61 $p |- ( -. ( ph -> ps ) <-> ( ph /\ -. ps ) ) $=
    ( wn wa wi annim bicomi ) ABCDABECABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *4.65 of [WhiteheadRussell] p. 120. $)
  pm4.65 $p |- ( -. ( -. ph -> ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wn pm4.61 ) ACBD $.
    $( [3-Jan-2005] $)

  $( Theorem *4.14 of [WhiteheadRussell] p. 117.  (The proof was shortened by
     Wolf Lammen, 23-Oct-2012.) $)
  pm4.14 $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    ( wi wn wa con34b imbi2i impexp 3bitr4i ) ABCDZDACEZBEZDZDABFCDALFMDKNABCGH
    ABCIALMIJ $.
    $( [23-Oct-2012] $) $( [3-Jan-2005] $)

  $( Theorem *3.37 (Transp) of [WhiteheadRussell] p. 112.  (The proof was
     shortened by Wolf Lammen, 23-Oct-2012.) $)
  pm3.37 $p |- ( ( ( ph /\ ps ) -> ch ) -> ( ( ph /\ -. ch ) -> -. ps ) ) $=
    ( wa wi wn pm4.14 biimpi ) ABDCEACFDBFEABCGH $.
    $( [23-Oct-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.15 of [WhiteheadRussell] p. 117.  (The proof was shortened by
     Wolf Lammen, 18-Nov-2012.) $)
  pm4.15 $p |- ( ( ( ph /\ ps ) -> -. ch ) <-> ( ( ps /\ ch ) -> -. ph ) ) $=
    ( wa wn wi con2b nan bitr2i ) BCDZAEFAJEFABDCEFJAGABCHI $.
    $( [18-Nov-2012] $) $( [3-Jan-2005] $)

  ${
    condan.1 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    condan.2 $e |- ( ( ph /\ -. ps ) -> -. ch ) $.
    $( Proof by contradiction.  (The proof was shortened by Wolf Lammen,
       19-Jun-2014.) $)
    condan $p |- ( ph -> ps ) $=
      ( wn pm2.65da notnot2 syl ) ABFZFBAJCDEGBHI $.
      $( [19-Jun-2014] $) $( [9-Feb-2006] $)
  $}

  $( Conjunction distributes over exclusive-or, using ` -. ( ph <-> ps ) ` to
     express exclusive-or.  This is one way to interpret the distributive law
     of multiplication over addition in modulo 2 arithmetic. $)
  xordi $p |- ( ( ph /\ -. ( ps <-> ch ) ) <->
                -. ( ( ph /\ ps ) <-> ( ph /\ ch ) ) ) $=
    ( wb wn wa wi annim pm5.32 xchbinx ) ABCDZEFAKGABFACFDAKHABCIJ $.
    $( [3-Oct-2008] $)

  $( Theorem *2.54 of [WhiteheadRussell] p. 107. $)
  pm2.54 $p |- ( ( -. ph -> ps ) -> ( ph \/ ps ) ) $=
    ( wn wo notnot2 orc syl olc ja ) ACZBABDZJCAKAEABFGBAHI $.
    $( [3-Jan-2005] $)

  $( Define disjunction (logical 'or').  Definition of [Margaris] p. 49. $)
  df-or $p |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $=
    ( wo wn wi pm2.53 pm2.54 impbii ) ABCADBEABFABGH $.
    $( [31-Jan-2015] $)

  ${
    orrd.1 $e |- ( ph -> ( -. ps -> ch ) ) $.
    $( Deduce implication from disjunction. $)
    orrd $p |- ( ph -> ( ps \/ ch ) ) $=
      ( wn wi wo pm2.54 syl ) ABECFBCGDBCHI $.
      $( [27-Nov-1995] $)
  $}

  ${
    orri.1 $e |- ( -. ph -> ps ) $.
    $( Infer implication from disjunction. $)
    orri $p |- ( ph \/ ps ) $=
      ( wo wn wi df-or mpbir ) ABDAEBFCABGH $.
      $( [11-Jun-1994] $)
  $}

  $( Theorem *2.25 of [WhiteheadRussell] p. 104. $)
  pm2.25 $p |- ( ph \/ ( ( ph \/ ps ) -> ps ) ) $=
    ( wo wi orel1 orri ) AABCBDABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *2.68 of [WhiteheadRussell] p. 108. $)
  pm2.68 $p |- ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) ) $=
    ( wi jarl orrd ) ABCBCABABBDE $.
    $( [21-Oct-2012] $) $( [3-Jan-2005] $)

  $( Logical 'or' expressed in terms of implication only.  Theorem *5.25 of
     [WhiteheadRussell] p. 124.  (The proof was shortened by Wolf Lammen,
     20-Oct-2012.) $)
  dfor2 $p |- ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ) $=
    ( wo wi pm2.62 pm2.68 impbii ) ABCABDBDABEABFG $.
    $( [21-Oct-2012] $) $( [12-Aug-2004] $)

  $( Theorem *4.64 of [WhiteheadRussell] p. 120. $)
  pm4.64 $p |- ( ( -. ph -> ps ) <-> ( ph \/ ps ) ) $=
    ( wo wn wi df-or bicomi ) ABCADBEABFG $.
    $( [3-Jan-2005] $)

  $( Implication in terms of disjunction.  Theorem *4.6 of [WhiteheadRussell]
     p. 120. $)
  imor $p |- ( ( ph -> ps ) <-> ( -. ph \/ ps ) ) $=
    ( wi wn wo notnot imbi1i df-or bitr4i ) ABCADZDZBCJBEAKBAFGJBHI $.
    $( [5-Aug-1993] $)

  ${
    imori.1 $e |- ( ph -> ps ) $.
    $( Infer disjunction from implication. $)
    imori $p |- ( -. ph \/ ps ) $=
      ( wi wn wo imor mpbi ) ABDAEBFCABGH $.
      $( [12-Mar-2012] $)
  $}

  $( Law of excluded middle, also called the principle of _tertium non datur_.
     Theorem *2.11 of [WhiteheadRussell] p. 101.  It says that something is
     either true or not true; there are no in-between values of truth.  This is
     an essential distinction of our classical logic and is not a theorem of
     intuitionistic logic. $)
  exmid $p |- ( ph \/ -. ph ) $=
    ( wn id orri ) AABZECD $.
    $( [5-Aug-1993] $)

  $( Theorem *2.1 of [WhiteheadRussell] p. 101.  (The proof was shortened by
     Wolf Lammen, 23-Nov-2012.) $)
  pm2.1 $p |- ( -. ph \/ ph ) $=
    ( id imori ) AAABC $.
    $( [23-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *2.13 of [WhiteheadRussell] p. 101. $)
  pm2.13 $p |- ( ph \/ -. -. -. ph ) $=
    ( wn notnot1 orri ) AABZBBECD $.
    $( [3-Jan-2005] $)

  $( Theorem *4.62 of [WhiteheadRussell] p. 120. $)
  pm4.62 $p |- ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wn imor ) ABCD $.
    $( [3-Jan-2005] $)

  $( Theorem *4.66 of [WhiteheadRussell] p. 120. $)
  pm4.66 $p |- ( ( -. ph -> -. ps ) <-> ( ph \/ -. ps ) ) $=
    ( wn pm4.64 ) ABCD $.
    $( [3-Jan-2005] $)

  $( Negated conjunction in terms of disjunction (DeMorgan's law).  Theorem
     *4.51 of [WhiteheadRussell] p. 120.  (The proof was shortened by Andrew
     Salmon, 13-May-2011.) $)
  ianor $p |- ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wa wn wi wo imnan pm4.62 bitr3i ) ABCDABDZEADJFABGABHI $.
    $( [3-Nov-2012] $) $( [5-Aug-1993] $)

  $( Conjunction in terms of disjunction (DeMorgan's law).  Theorem *4.5 of
     [WhiteheadRussell] p. 120.  (The proof was shortened by Wolf Lammen,
     3-Nov-2012.) $)
  anor $p |- ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) ) $=
    ( wn wo wa ianor bicomi con2bii ) ACBCDZABEZJCIABFGH $.
    $( [3-Nov-2012] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ ioran as of 28-Sep-2014. $)
  ioranOLD $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wo wn wi wa df-or notbii annim bitr4i ) ABCZDADZBEZDLBDFKMABGHLBIJ $.
    $( [12-May-2011] $) $( [5-Aug-1993] $)

  $( Absorption of disjunction into equivalence.  (The proof was shortened by
     Wolf Lammen, 3-Nov-2013.) $)
  oibabs $p |- ( ( ( ph \/ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) ) $=
    ( wo wb wi wn wa ioran pm5.21 sylbi id ja ax-1 impbii ) ABCZABDZEPOPPOFAFBF
    GPABHABIJPKLPOMN $.
    $( [3-Nov-2013] $)  $( [6-Aug-1995] $)

  $( Theorem *4.52 of [WhiteheadRussell] p. 120.  (The proof was shortened by
     Wolf Lammen, 5-Nov-2012.) $)
  pm4.52 $p |- ( ( ph /\ -. ps ) <-> -. ( -. ph \/ ps ) ) $=
    ( wn wa wi wo annim imor xchbinx ) ABCDABEACBFABGABHI $.
    $( [5-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.53 of [WhiteheadRussell] p. 120. $)
  pm4.53 $p |- ( -. ( ph /\ -. ps ) <-> ( -. ph \/ ps ) ) $=
    ( wn wo wa pm4.52 con2bii bicomi ) ACBDZABCEZCJIABFGH $.
    $( [3-Jan-2005] $)

  $( Theorem *4.54 of [WhiteheadRussell] p. 120.  (The proof was shortened by
     Wolf Lammen, 5-Nov-2012.) $)
  pm4.54 $p |- ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) $=
    ( wn wa wi wo df-an pm4.66 xchbinx ) ACZBDJBCZEAKFJBGABHI $.
    $( [28-Sep-2014] $) $( [3-Jan-2005] $)

  $( Obsolete proof of ~ pm4.54 as of 28-Sep-2014. $)
  pm4.54OLD $p |- ( ( -. ph /\ ps ) <-> -. ( ph \/ -. ps ) ) $=
    ( wn wa wi wo pm4.67 pm4.66 notbii bitr3i ) ACZBDKBCZEZCALFZCABGMNABHIJ $.
    $( [5-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.55 of [WhiteheadRussell] p. 120. $)
  pm4.55 $p |- ( -. ( -. ph /\ ps ) <-> ( ph \/ -. ps ) ) $=
    ( wn wo wa pm4.54 con2bii bicomi ) ABCDZACBEZCJIABFGH $.
    $( [3-Jan-2005] $)

  $( Theorem *4.56 of [WhiteheadRussell] p. 120. $)
  pm4.56 $p |- ( ( -. ph /\ -. ps ) <-> -. ( ph \/ ps ) ) $=
    ( wo wn wa ioran bicomi ) ABCDADBDEABFG $.
    $( [3-Jan-2005] $)

  $( Disjunction in terms of conjunction (DeMorgan's law).  Compare Theorem
     *4.57 of [WhiteheadRussell] p. 120.  (The proof was shortened by Andrew
     Salmon, 7-May-2011.) $)
  oran $p |- ( ( ph \/ ps ) <-> -. ( -. ph /\ -. ps ) ) $=
    ( wn wa wo pm4.56 con2bii ) ACBCDABEABFG $.
    $( [12-May-2011] $) $( [5-Aug-1993] $)

  $( Theorem *4.57 of [WhiteheadRussell] p. 120. $)
  pm4.57 $p |- ( -. ( -. ph /\ -. ps ) <-> ( ph \/ ps ) ) $=
    ( wo wn wa oran bicomi ) ABCADBDEDABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *3.11 of [WhiteheadRussell] p. 111. $)
  pm3.11 $p |- ( -. ( -. ph \/ -. ps ) -> ( ph /\ ps ) ) $=
    ( wa wn wo anor biimpri ) ABCADBDEDABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *3.12 of [WhiteheadRussell] p. 111. $)
  pm3.12 $p |- ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) $=
    ( wn wo wa pm3.11 orri ) ACBCDABEABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *3.13 of [WhiteheadRussell] p. 111. $)
  pm3.13 $p |- ( -. ( ph /\ ps ) -> ( -. ph \/ -. ps ) ) $=
    ( wn wo wa pm3.11 con1i ) ACBCDABEABFG $.
    $( [3-Jan-2005] $)

  $( Theorem *4.78 of [WhiteheadRussell] p. 121.  (The proof was shortened by
     Wolf Lammen, 19-Nov-2012.) $)
  pm4.78 $p |- ( ( ( ph -> ps ) \/ ( ph -> ch ) ) <->
                ( ph -> ( ps \/ ch ) ) ) $=
    ( wn wo wi orordi imor orbi12i 3bitr4ri ) ADZBCEZEKBEZKCEZEALFABFZACFZEKBCG
    ALHOMPNABHACHIJ $.
    $( [19-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.79 of [WhiteheadRussell] p. 121.  (The proof was shortened by
     Wolf Lammen, 27-Jun-2013.) $)
  pm4.79 $p |- ( ( ( ps -> ph ) \/ ( ch -> ph ) ) <->
                ( ( ps /\ ch ) -> ph ) ) $=
    ( wi wo wa id jaoa wn simplim pm3.3 syl5 orrd impbii ) BADZCADZEBCFADZOBAPC
    OGPGHQOPOIBQPBAJBCAKLMN $.
    $( [27-Jun-2013] $) $( [3-Jan-2005] $)

  $( Theorem *5.17 of [WhiteheadRussell] p. 124.  (The proof was shortened by
     Wolf Lammen, 3-Jan-2013.) $)
  pm5.17 $p |- ( ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) <-> ( ph <-> -. ps ) ) $=
    ( wn wb wi wa wo bicom dfbi2 orcom df-or bitr2i imnan anbi12i 3bitrri ) ABC
    ZDPADPAEZAPEZFABGZABFCZFAPHPAIQSRTSBAGQABJBAKLABMNO $.
    $( [3-Jan-2013] $) $( [3-Jan-2005] $)

  $( Disjunction distributes over implication.  (Contributed by Wolf Lammen,
     5-Jan-2013.) $)
  orimdi $p |- ( ( ph \/ ( ps -> ch ) ) <->
                ( ( ph \/ ps ) -> ( ph \/ ch ) ) ) $=
    ( wn wi wo imdi df-or imbi12i 3bitr4i ) ADZBCEZEKBEZKCEZEALFABFZACFZEKBCGAL
    HOMPNABHACHIJ $.
    $( [5-Jan-2013] $)

  $( Theorem *2.85 of [WhiteheadRussell] p. 108.  (The proof was shortened by
     Wolf Lammen, 5-Jan-2013.) $)
  pm2.85 $p |- ( ( ( ph \/ ps ) -> ( ph \/ ch ) ) ->
                ( ph \/ ( ps -> ch ) ) ) $=
    ( wi wo orimdi biimpri ) ABCDEABEACEDABCFG $.
    $( [5-Jan-2013] $) $( [3-Jan-2005] $)

  $( Two ways to express "exclusive or."  Theorem *5.22 of [WhiteheadRussell]
     p. 124.  (The proof was shortened by Wolf Lammen, 22-Jan-2013.) $)
  xor $p |- ( -. ( ph <-> ps ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wn wa wo wb wi iman anbi12i dfbi2 ioran 3bitr4ri con1bii ) ABCDZBACDZEZAB
    FZABGZBAGZDNCZOCZDQPCRTSUAABHBAHIABJNOKLM $.
    $( [22-Jan-2013] $) $( [3-Jan-2005] $)

  $( Two ways to express "exclusive or."  (The proof was shortened by Wolf
     Lammen, 24-Jan-2013.) $)
  xor2 $p |- ( -. ( ph <-> ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $=
    ( wb wn wo wa xor3 pm5.17 bitr4i ) ABCDABDCABEABFDFABGABHI $.
    $( [24-Jan-2013] $) $( [3-Jan-2005] $)

  $( An alternate definition of the biconditional.  Theorem *5.23 of
     [WhiteheadRussell] p. 124.  (The proof was shortened by Wolf Lammen,
     3-Nov-2013.) $)
  dfbi3 $p |- ( ( ph <-> ps ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) ) $=
    ( wn wb wa wo xor pm5.18 notnot anbi2i ancom orbi12i 3bitr4i ) ABCZDCANCZEZ
    NACZEZFABDABEZQNEZFANGABHSPTRBOABIJQNKLM $.
    $( [3-Nov-2013] $) $( [27-Jun-2002] $)

  $( Theorem *5.24 of [WhiteheadRussell] p. 124. $)
  pm5.24 $p |- ( -. ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) <->
                ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wb wn wa wo xor dfbi3 xchnxbi ) ABCABDZEBADZEFABEKJEFABGABHI $.
    $( [3-Jan-2005] $)

  $( Obsolete proof of ~ jcab as of 27-Nov-2013 $)
  jcabOLD $p |- ( ( ph -> ( ps /\ ch ) ) <->
                 ( ( ph -> ps ) /\ ( ph -> ch ) ) ) $=
    ( wn wa wo wi ordi imor anbi12i 3bitr4i ) ADZBCEZFLBFZLCFZEAMGABGZACGZELBCH
    AMIPNQOABIACIJK $.
    $( [3-Apr-1994] $)

  $( Simplify an implication between implications.  (Contributed by Paul
     Chapman, 17-Nov-2012.)  (The proof was shortened by Wolf Lammen,
     3-Apr-2013.) $)
  imimorb $p |- ( ( ( ps -> ch ) -> ( ph -> ch ) ) <->
                  ( ph -> ( ps \/ ch ) ) ) $=
    ( wi wo bi2.04 dfor2 imbi2i bitr4i ) BCDZACDDAJCDZDABCEZDJACFLKABCGHI $.
    $( [3-Apr-2013] $) $( [17-Nov-2012] $)

  $( Theorem *2.26 of [WhiteheadRussell] p. 104.  (The proof was shortened by
     Wolf Lammen, 23-Nov-2012.) $)
  pm2.26 $p |- ( -. ph \/ ( ( ph -> ps ) -> ps ) ) $=
    ( wi pm2.27 imori ) AABCBCABDE $.
    $( [23-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *5.11 of [WhiteheadRussell] p. 123. $)
  pm5.11 $p |- ( ( ph -> ps ) \/ ( -. ph -> ps ) ) $=
    ( wi wn pm2.5 orri ) ABCADBCABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *5.12 of [WhiteheadRussell] p. 123. $)
  pm5.12 $p |- ( ( ph -> ps ) \/ ( ph -> -. ps ) ) $=
    ( wi wn pm2.51 orri ) ABCABDCABEF $.
    $( [3-Jan-2005] $)

  $( Theorem *5.14 of [WhiteheadRussell] p. 123. $)
  pm5.14 $p |- ( ( ph -> ps ) \/ ( ps -> ch ) ) $=
    ( wi wn ax-1 con3i pm2.21d orri ) ABDZBCDJEBCBJBAFGHI $.
    $( [3-Jan-2005] $)

  $( Theorem *5.13 of [WhiteheadRussell] p. 123.  (The proof was shortened by
     Wolf Lammen, 14-Nov-2012.) $)
  pm5.13 $p |- ( ( ph -> ps ) \/ ( ps -> ph ) ) $=
    ( pm5.14 ) ABAC $.
    $( [14-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *5.15 of [WhiteheadRussell] p. 124.  (The proof was shortened by
     Wolf Lammen, 15-Oct-2013.) $)
  pm5.15 $p |- ( ( ph <-> ps ) \/ ( ph <-> -. ps ) ) $=
    ( wb wn xor3 biimpi orri ) ABCZABDCZHDIABEFG $.
    $( [15-Oct-2013] $) $( [3-Jan-2005] $)

  $( Theorem *5.55 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 20-Jan-2013.) $)
  pm5.55 $p |- ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) ) $=
    ( wo wb biort bicomd wn biorf nsyl4 con1i orri ) ABCZADZLBDZNMAMNAALABEFAGB
    LABHFIJK $.
    $( [20-Jan-2013] $) $( [3-Jan-2005] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Miscellaneous theorems of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    pm5.21nd.1 $e |- ( ( ph /\ ps ) -> th ) $.
    pm5.21nd.2 $e |- ( ( ph /\ ch ) -> th ) $.
    pm5.21nd.3 $e |- ( th -> ( ps <-> ch ) ) $.
    $( Eliminate an antecedent implied by each side of a biconditional.  (The
       proof was shortened by Wolf Lammen, 4-Nov-2013.) $)
    pm5.21nd $p |- ( ph -> ( ps <-> ch ) ) $=
      ( ex wb wi a1i pm5.21ndd ) ADBCABDEHACDFHDBCIJAGKL $.
      $( [4-Nov-2013] $) $( [20-Nov-2005] $)
  $}

  $( Theorem *5.35 of [WhiteheadRussell] p. 125. $)
  pm5.35 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) ->
                ( ph -> ( ps <-> ch ) ) ) $=
    ( wi wa pm5.1 pm5.74rd ) ABDZACDZEABCHIFG $.
    $( [3-Jan-2005] $)

  $( Theorem *5.54 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 7-Nov-2013.) $)
  pm5.54 $p |- ( ( ( ph /\ ps ) <-> ph ) \/ ( ( ph /\ ps ) <-> ps ) ) $=
    ( wa wb iba bicomd adantl pm5.21ni orri ) ABCZADZJBDJKBBKABAJBAEFZGLHI $.
    $( [7-Nov-2013] $) $( [3-Jan-2005] $)

  ${
    baib.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional. $)
    baib $p |- ( ps -> ( ph <-> ch ) ) $=
      ( wa ibar syl6rbbr ) BCBCEABCFDG $.
      $( [13-May-1999] $)
  $}

  ${
    baibr.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Move conjunction outside of biconditional. $)
    baibr $p |- ( ps -> ( ch <-> ph ) ) $=
      ( baib bicomd ) BACABCDEF $.
      $( [11-Jul-1994] $)
  $}

  $( Theorem *5.44 of [WhiteheadRussell] p. 125. $)
  pm5.44 $p |- ( ( ph -> ps ) -> ( ( ph -> ch ) <->
                ( ph -> ( ps /\ ch ) ) ) ) $=
    ( wa wi jcab baibr ) ABCDEABEACEABCFG $.
    $( [3-Jan-2005] $)

  $( Conjunction in antecedent versus disjunction in consequent.  Theorem *5.6
     of [WhiteheadRussell] p. 125. $)
  pm5.6 $p |- ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) ) $=
    ( wn wa wi wo impexp df-or imbi2i bitr4i ) ABDZECFALCFZFABCGZFALCHNMABCIJK
    $.
    $( [22-Mar-2005] $) $( [8-Jun-1994] $)

  ${
    orcanai.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    $( Change disjunction in consequent to conjunction in antecedent. $)
    orcanai $p |- ( ( ph /\ -. ps ) -> ch ) $=
      ( wn ord imp ) ABECABCDFG $.
      $( [8-Jun-1994] $)
  $}


  ${
    intnan.1 $e |- -. ph $.
    $( Introduction of conjunct inside of a contradiction. $)
    intnan $p |- -. ( ps /\ ph ) $=
      ( wa simpr mto ) BADACBAEF $.
      $( [16-Sep-1993] $)

    $( Introduction of conjunct inside of a contradiction. $)
    intnanr $p |- -. ( ph /\ ps ) $=
      ( wa simpl mto ) ABDACABEF $.
      $( [3-Apr-1995] $)
  $}

  ${
    intnand.1 $e |- ( ph -> -. ps ) $.
    $( Introduction of conjunct inside of a contradiction. $)
    intnand $p |- ( ph -> -. ( ch /\ ps ) ) $=
      ( wa simpr nsyl ) ABCBEDCBFG $.
      $( [10-Jul-2005] $)

    $( Introduction of conjunct inside of a contradiction. $)
    intnanrd $p |- ( ph -> -. ( ps /\ ch ) ) $=
      ( wa simpl nsyl ) ABBCEDBCFG $.
      $( [10-Jul-2005] $)
  $}

  ${
    mpbiran.1 $e |- ps $.
    mpbiran.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional. $)
    mpbiran $p |- ( ph <-> ch ) $=
      ( wa biantrur bitr4i ) ABCFCEBCDGH $.
      $( [9-Jan-2015] $) $( [27-Feb-1996] $)
  $}

  ${
    mpbiran2.1 $e |- ch $.
    mpbiran2.2 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach truth from conjunction in biconditional. $)
    mpbiran2 $p |- ( ph <-> ps ) $=
      ( wa biantru bitr4i ) ABCFBECBDGH $.
      $( [9-Jan-2015] $) $( [22-Feb-1996] $)
  $}

  ${
    mpbir2an.1 $e |- ps $.
    mpbir2an.2 $e |- ch $.
    mpbiran2an.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( Detach a conjunction of truths in a biconditional. $)
    mpbir2an $p |- ph $=
      ( mpbiran mpbir ) ACEABCDFGH $.
      $( [9-Jan-2015] $) $( [10-May-2005] $)
  $}

  ${
    mpbi2and.1 $e |- ( ph -> ps ) $.
    mpbi2and.2 $e |- ( ph -> ch ) $.
    mpbi2and.3 $e |- ( ph -> ( ( ps /\ ch ) <-> th ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (The proof was
       shortened by Wolf Lammen, 24-Nov-2012.) $)
    mpbi2and $p |- ( ph -> th ) $=
      ( wa jca mpbid ) ABCHDABCEFIGJ $.
      $( [9-Jan-2015] $) $( [6-Nov-2011] $)
  $}

  ${
    mpbir2and.1 $e |- ( ph -> ch ) $.
    mpbir2and.2 $e |- ( ph -> th ) $.
    mpbir2and.3 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (The proof was
       shortened by Wolf Lammen, 24-Nov-2012.) $)
    mpbir2and $p |- ( ph -> ps ) $=
      ( wa jca mpbird ) ABCDHACDEFIGJ $.
      $( [9-Jan-2015] $)  $( [6-Nov-2011] $)
  $}

  ${
    mpbiranOLD.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    ${
      mpbiranOLD.2 $e |- ps $.
      $( Obsolete version of ~ mpbiran as of 9-Jan-2015. $)
      mpbiranOLD $p |- ( ph <-> ch ) $=
        ( mpbiran ) ABCEDF $.
        $( [27-Feb-1996] $)
    $}

    ${
      mpbiran2OLD.2 $e |- ch $.
      $( Obsolete version of ~ mpbiran2 as of 9-Jan-2015. $)
      mpbiran2OLD $p |- ( ph <-> ps ) $=
        ( mpbiran2 ) ABCEDF $.
        $( [22-Feb-1996] $)
    $}

    ${
      mpbir2anOLD.2 $e |- ps $.
      mpbir2anOLD.3 $e |- ch $.
      $( Obsolete version of ~ mpbir2an as of 9-Jan-2015. $)
      mpbir2anOLD $p |- ph $=
        ( mpbir2an ) ABCEFDG $.
        $( [10-May-2005] $)
    $}
  $}

  ${
    mpbi2andOLD.1 $e |- ( ph -> ( ( ps /\ ch ) <-> th ) ) $.
    mpbi2andOLD.2 $e |- ( ph -> ps ) $.
    mpbi2andOLD.3 $e |- ( ph -> ch ) $.
    $( Obsolete version of ~ mpbi2and as of 9-Jan-2015. $)
    mpbi2andOLD $p |- ( ph -> th ) $=
      ( mpbi2and ) ABCDFGEH $.
      $( [24-Nov-2012] $) $( [6-Nov-2011] $)
  $}

  ${
    mpbir2andOLD.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    mpbir2andOLD.2 $e |- ( ph -> ch ) $.
    mpbir2andOLD.3 $e |- ( ph -> th ) $.
    $( Obsolete version of ~ mpbir2and as of 9-Jan-2015. $)
    mpbir2andOLD $p |- ( ph -> ps ) $=
      ( mpbir2and ) ABCDFGEH $.
      $( [24-Nov-2012] $) $( [6-Nov-2011] $)
  $}

  $( Theorem *5.62 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm5.62 $p |- ( ( ( ph /\ ps ) \/ -. ps ) <-> ( ph \/ -. ps ) ) $=
    ( wa wn wo exmid ordir mpbiran2 ) ABCBDZEAIEBIEBFABIGH $.
    $( [21-Jun-2005] $)

  $( Theorem *5.63 of [WhiteheadRussell] p. 125.  (The proof was shortened by
     Wolf Lammen, 25-Dec-2012.) $)
  pm5.63 $p |- ( ( ph \/ ps ) <-> ( ph \/ ( -. ph /\ ps ) ) ) $=
    ( wn wa wo exmid ordi mpbiran bicomi ) AACZBDEZABEZKAJELAFAJBGHI $.
    $( [25-Dec-2012] $) $( [3-Jan-2005] $)

  ${
    bianfi.1 $e |- -. ph $.
    $( A wff conjoined with falsehood is false.  (The proof was shortened by
       Wolf Lammen, 26-Nov-2012.) $)
    bianfi $p |- ( ph <-> ( ps /\ ph ) ) $=
      ( wa intnan 2false ) ABADCABCEF $.
      $( [26-Nov-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    bianfd.1 $e |- ( ph -> -. ps ) $.
    $( A wff conjoined with falsehood is false.  (The proof was shortened by
       Wolf Lammen, 5-Nov-2013.) $)
    bianfd $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $=
      ( wa intnanrd 2falsed ) ABBCEDABCDFG $.
      $( [5-Nov-2013] $) $( [27-Mar-1995] $)
  $}

  $( Theorem *4.43 of [WhiteheadRussell] p. 119.  (The proof was shortened by
     Wolf Lammen, 26-Nov-2012.) $)
  pm4.43 $p |- ( ph <-> ( ( ph \/ ps ) /\ ( ph \/ -. ps ) ) ) $=
    ( wn wa wo pm3.24 biorfi ordi bitri ) AABBCZDZEABEAJEDKABFGABJHI $.
    $( [26-Nov-2012] $) $( [3-Jan-2005] $)

  $( Theorem *4.82 of [WhiteheadRussell] p. 122. $)
  pm4.82 $p |- ( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph ) $=
    ( wi wn wa pm2.65 imp pm2.21 jca impbii ) ABCZABDZCZEADZKMNABFGNKMABHALHIJ
    $.
    $( [3-Jan-2005] $)

  $( Theorem *4.83 of [WhiteheadRussell] p. 122. $)
  pm4.83 $p |- ( ( ( ph -> ps ) /\ ( -. ph -> ps ) ) <-> ps ) $=
    ( wn wo wi wa exmid a1bi jaob bitr2i ) BAACZDZBEABEKBEFLBAGHABKIJ $.
    $( [3-Jan-2005] $)

  $( Negation inferred from embedded conjunct.  (The proof was shortened by
     Wolf Lammen, 25-Nov-2012.) $)
  pclem6 $p |- ( ( ph <-> ( ps /\ -. ph ) ) -> -. ps ) $=
    ( wn wa wb ibar nbbn sylib con2i ) BABACZDZEZBJKELCBJFAKGHI $.
    $( [25-Nov-2012] $) $( [20-Aug-1993] $)

  $( A transitive law of equivalence.  Compare Theorem *4.22 of
     [WhiteheadRussell] p. 117. $)
  biantr $p |- ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) ) $=
    ( wb id bibi2d biimparc ) CBDZACDABDHCBAHEFG $.
    $( [18-Aug-1993] $)

  $( Disjunction distributes over the biconditional.  An axiom of system DS in
     Vladimir Lifschitz, "On calculational proofs" (1998),
     ~ http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.3384 .  (The
     proof was shortened by Wolf Lammen, 4-Feb-2013.) $)
  orbidi $p |- ( ( ph \/ ( ps <-> ch ) ) <->
                ( ( ph \/ ps ) <-> ( ph \/ ch ) ) ) $=
    ( wn wb wi wo pm5.74 df-or bibi12i 3bitr4i ) ADZBCEZFLBFZLCFZEAMGABGZACGZEL
    BCHAMIPNQOABIACIJK $.
    $( [4-Feb-2013] $) $( [8-Jan-2005] $)

  $( Lukasiewicz's shortest axiom for equivalential calculus.  Storrs McCall,
     ed., _Polish Logic 1920-1939_ (Oxford, 1967), p. 96. $)
  biluk $p |- ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) ) $=
    ( wb bicom bibi1i biass bitri mpbi bitr4i ) ABDZCBACDZDZDZCBDLDKCDZMDKNDOBA
    DZCDMKPCABEFBACGHKCMGICBLGJ $.
    $( [10-Jan-2005] $)

  $( Disjunction distributes over the biconditional.  Theorem *5.7 of
     [WhiteheadRussell] p. 125.  This theorem is similar to ~ orbidi .
     (Contributed by Roy F. Longton, 21-Jun-2005.) $)
  pm5.7 $p |- ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <->
               ( ch \/ ( ph <-> ps ) ) ) $=
    ( wb wo orbidi orcom bibi12i bitr2i ) CABDECAEZCBEZDACEZBCEZDCABFJLKMCAGCBG
    HI $.
    $( [21-Jun-2005] $)

  $( Dijkstra-Scholten's Golden Rule for calculational proofs. $)
  bigolden $p |- ( ( ( ph /\ ps ) <-> ph ) <-> ( ps <-> ( ph \/ ps ) ) ) $=
    ( wi wa wb wo pm4.71 pm4.72 bicom 3bitr3ri ) ABCAABDZEBABFEKAEABGABHAKIJ $.
    $( [10-Jan-2005] $)

  $( Theorem *5.71 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 23-Jun-2005.) $)
  pm5.71 $p |- ( ( ps -> -. ch ) -> ( ( ( ph \/ ps ) /\ ch ) <->
                ( ph /\ ch ) ) ) $=
    ( wn wo wa wb orel2 orc impbid1 anbi1d pm2.21 pm5.32rd ja ) BCDZABEZCFACFGB
    DZPACQPABAHABIJKOCPACPAGLMN $.
    $( [23-Jun-2005] $)

  $( Theorem *5.75 of [WhiteheadRussell] p. 126.  (The proof was shortened by
     Andrew Salmon, 7-May-2011.)  (The proof was shortened by Wolf Lammen,
     23-Dec-2012.) $)
  pm5.75 $p |- ( ( ( ch -> -. ps ) /\ ( ph <-> ( ps \/ ch ) ) ) ->
                ( ( ph /\ -. ps ) <-> ch ) ) $=
    ( wo wb wn wa wi anbi1 anbi1i pm5.61 syl6bb pm4.71 biimpi bicomd sylan9bbr
    orcom bitri ) ABCDZEZABFZGZCUAGZCUAHZCTUBSUAGZUCASUAIUECBDZUAGUCSUFUABCQJCB
    KRLUDCUCUDCUCECUAMNOP $.
    $( [23-Dec-2012] $) $( [3-Jan-2005] $)

  $( Removal of conjunct from one side of an equivalence. $)
  bimsc1 $p |- ( ( ( ph -> ps ) /\ ( ch <-> ( ps /\ ph ) ) )
               -> ( ch <-> ph ) ) $=
    ( wi wa wb simpr ancr impbid2 bibi2d biimpa ) ABDZCBAEZFCAFLMACLMABAGABHIJK
    $.
    $( [5-Aug-1993] $)

  $( The disjunction of the four possible combinations of two wffs and their
     negations is always true.  (Contributed by David Abernethy,
     28-Jan-2014.) $)
  4exmid $p |- ( ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) )
              \/ ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $=
    ( wb wn wo wa exmid dfbi3 xor orbi12i mpbi ) ABCZLDZEABFADZBDZFEZAOFBNFEZEL
    GLPMQABHABIJK $.
    $( [1-Feb-2014] $)

  ${
    ecase2d.1 $e |- ( ph -> ps ) $.
    ecase2d.2 $e |- ( ph -> -. ( ps /\ ch ) ) $.
    ecase2d.3 $e |- ( ph -> -. ( ps /\ th ) ) $.
    ecase2d.4 $e |- ( ph -> ( ta \/ ( ch \/ th ) ) ) $.
    $( Deduction for elimination by cases.  (The proof was shortened by Wolf
       Lammen, 22-Dec-2012.) $)
    ecase2d $p |- ( ph -> ta ) $=
      ( wo wn wa wi imnan sylibr mpd ioran sylanbrc ord mt3d ) AECDJZACKZDKZUAK
      ABUBFABCLKBUBMGBCNOPABUCFABDLKBUCMHBDNOPCDQRAEUAIST $.
      $( [22-Dec-2012] $) $( [21-Apr-1994] $)
  $}

  ${
    ecase3.1 $e |- ( ph -> ch ) $.
    ecase3.2 $e |- ( ps -> ch ) $.
    ecase3.3 $e |- ( -. ( ph \/ ps ) -> ch ) $.
    $( Inference for elimination by cases.  (The proof was shortened by Wolf
       Lammen, 26-Nov-2012.) $)
    ecase3 $p |- ch $=
      ( wo jaoi pm2.61i ) ABGCACBDEHFI $.
      $( [26-Nov-2012] $) $( [23-Mar-1995] $)
  $}

  ${
    ecase.1 $e |- ( -. ph -> ch ) $.
    ecase.2 $e |- ( -. ps -> ch ) $.
    ecase.3 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference for elimination by cases. $)
    ecase $p |- ch $=
      ( ex pm2.61nii ) ABCABCFGDEH $.
      $( [13-Jul-2005] $)
  $}

  ${
    ecase3d.1 $e |- ( ph -> ( ps -> th ) ) $.
    ecase3d.2 $e |- ( ph -> ( ch -> th ) ) $.
    ecase3d.3 $e |- ( ph -> ( -. ( ps \/ ch ) -> th ) ) $.
    $( Deduction for elimination by cases.  (The proof was shortened by Andrew
       Salmon, 7-May-2011.) $)
    ecase3d $p |- ( ph -> th ) $=
      ( wo jaod pm2.61d ) ABCHDABDCEFIGJ $.
      $( [12-May-2011] $) $( [2-May-1996] $)
  $}

  ${
    ecased.1 $e |- ( ph -> ( -. ps -> th ) ) $.
    ecased.2 $e |- ( ph -> ( -. ch -> th ) ) $.
    ecased.3 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Deduction for elimination by cases. $)
    ecased $p |- ( ph -> th ) $=
      ( wn wo wa pm3.11 syl5 ecase3d ) ABHZCHZDEFNOIHBCJADBCKGLM $.
      $( [8-Oct-2012] $)
  $}

  ${
    ecase3ad.1 $e |- ( ph -> ( ps -> th ) ) $.
    ecase3ad.2 $e |- ( ph -> ( ch -> th ) ) $.
    ecase3ad.3 $e |- ( ph -> ( ( -. ps /\ -. ch ) -> th ) ) $.
    $( Deduction for elimination by cases. $)
    ecase3ad $p |- ( ph -> th ) $=
      ( wn notnot2 syl5 ecased ) ABHZCHZDLHBADBIEJMHCADCIFJGK $.
      $( [24-May-2013] $)
  $}

  ${
    ccase.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase.2 $e |- ( ( ch /\ ps ) -> ta ) $.
    ccase.3 $e |- ( ( ph /\ th ) -> ta ) $.
    ccase.4 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Inference for combining cases.  (The proof was shortened by Wolf Lammen,
       6-Jan-2013.) $)
    ccase $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      ( wo jaoian jaodan ) ACJBEDABECFGKADECHIKL $.
      $( [6-Jan-2013] $) $( [29-Jul-1999] $)
  $}

  ${
    ccased.1 $e |- ( ph -> ( ( ps /\ ch ) -> et ) ) $.
    ccased.2 $e |- ( ph -> ( ( th /\ ch ) -> et ) ) $.
    ccased.3 $e |- ( ph -> ( ( ps /\ ta ) -> et ) ) $.
    ccased.4 $e |- ( ph -> ( ( th /\ ta ) -> et ) ) $.
    $( Deduction for combining cases. $)
    ccased $p |- ( ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et ) ) $=
      ( wo wa wi com12 ccase ) BDKCEKLAFBCDEAFMABCLFGNADCLFHNABELFINADELFJNON
      $.
      $( [9-May-2004] $)
  $}

  ${
    ccase2.1 $e |- ( ( ph /\ ps ) -> ta ) $.
    ccase2.2 $e |- ( ch -> ta ) $.
    ccase2.3 $e |- ( th -> ta ) $.
    $( Inference for combining cases. $)
    ccase2 $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $=
      ( adantr adantl ccase ) ABCDEFCEBGIDEAHJDECHJK $.
      $( [29-Jul-1999] $)
  $}

  ${
    4cases.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    4cases.2 $e |- ( ( ph /\ -. ps ) -> ch ) $.
    4cases.3 $e |- ( ( -. ph /\ ps ) -> ch ) $.
    4cases.4 $e |- ( ( -. ph /\ -. ps ) -> ch ) $.
    $( Inference eliminating two antecedents from the four possible cases that
       result from their true/false combinations. $)
    4cases $p |- ch $=
      ( pm2.61ian wn pm2.61i ) BCABCDFHABICEGHJ $.
      $( [25-Oct-2003] $)
  $}

  ${
    4casesdan.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    4casesdan.2 $e |- ( ( ph /\ ( ps /\ -. ch ) ) -> th ) $.
    4casesdan.3 $e |- ( ( ph /\ ( -. ps /\ ch ) ) -> th ) $.
    4casesdan.4 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
    $( Deduction eliminating two antecedents from the four possible cases that
       result from their true/false combinations. $)
    4casesdan $p |- ( ph -> th ) $=
      ( wi wa expcom wn 4cases ) BCADIABCJDEKABCLZJDFKABLZCJDGKAONJDHKM $.
      $( [19-Mar-2013] $)
  $}

  ${
    niabn.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods. $)
    niabn $p |- ( -. ps -> ( ( ch /\ ps ) <-> -. ph ) ) $=
      ( wa wn simpr pm2.24i pm5.21ni ) CBEBAFCBGABDHI $.
      $( [31-Mar-1994] $)
  $}

  $( Lemma for an alternate version of weak deduction theorem.  (The proof was
     shortened by Andrew Salmon, 7-May-2011.)  (The proof was shortened by Wolf
     Lammen, 4-Dec-2012.) $)
  dedlem0a $p |- ( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\ ph ) ) ) ) $=
    ( wa wi iba wb ax-1 biimt syl bitrd ) ABBADZCAEZLEZABFAMLNGACHMLIJK $.
    $( [4-Dec-2012] $) $( [2-Apr-1994] $)

  $( Lemma for an alternate version of weak deduction theorem. $)
  dedlem0b $p |- ( -. ph -> ( ps <-> ( ( ps -> ph ) -> ( ch /\ ph ) ) ) ) $=
    ( wn wi wa pm2.21 imim2d com23 simpr imim12i con1d com12 impbid ) ADZBBAEZC
    AFZEZOPBQOAQBAQGHIROBRBABDPQABAGCAJKLMN $.
    $( [2-Apr-1994] $)

  $( Lemma for weak deduction theorem.  (The proof was shortened by Andrew
     Salmon, 7-May-2011.) $)
  dedlema $p |- ( ph -> ( ps <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wa wn wo orc expcom wi simpl a1i pm2.24 adantld jaod impbid ) ABBADZCAEZD
    ZFZBASPRGHAPBRPBIABAJKAQBCABLMNO $.
    $( [12-May-2011] $) $( [26-Jun-2002] $)

  $( Lemma for weak deduction theorem.  (The proof was shortened by Andrew
     Salmon, 7-May-2011.) $)
  dedlemb $p |- ( -. ph -> ( ch <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $=
    ( wn wa wo olc expcom pm2.21 adantld wi simpl a1i jaod impbid ) ADZCBAEZCPE
    ZFZCPSRQGHPQCRPACBACIJRCKPCPLMNO $.
    $( [12-May-2011] $) $( [15-May-1999] $)

  ${
    elimh.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( ch <-> ta ) ) $.
    elimh.2 $e |- ( ( ps <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    elimh.3 $e |- th $.
    $( Hypothesis builder for weak deduction theorem.  For more information,
       see the Deduction Theorem link on the Metamath Proof Explorer home
       page. $)
    elimh $p |- ta $=
      ( wa wn wo wb dedlema syl ibi dedlemb mpbii pm2.61i ) CECECAACIBCJZIKZLCE
      LCABMFNOSDEHSBTLDELCABPGNQR $.
      $( [26-Jun-2002] $)
  $}

  ${
    dedt.1 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) )
                     -> ( th <-> ta ) ) $.
    dedt.2 $e |- ta $.
    $( The weak deduction theorem.  For more information, see the Deduction
       Theorem link on the Metamath Proof Explorer home page. $)
    dedt $p |- ( ch -> th ) $=
      ( wa wn wo wb dedlema mpbiri syl ) CAACHBCIHJKZDCABLODEGFMN $.
      $( [26-Jun-2002] $)
  $}

  $( Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This version
     of ~ con3 demonstrates the use of the weak deduction theorem to derive it
     from ~ con3i . $)
  con3th $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi wn wa wo wb id notbid imbi1d imbi2d elimh con3i dedt ) BAABCZBDZADZCBO
    EAODEFZDZQCBRGZPSQTBRTHZIJARBAOAACARCTBRAUAKARGZARAUBHKAHLMN $.
    $( [27-Jun-2002] $)

  $( The consensus theorem.  This theorem and its dual (with ` \/ ` and ` /\ `
     interchanged) are commonly used in computer logic design to eliminate
     redundant terms from Boolean expressions.  Specifically, we prove that the
     term ` ( ps /\ ch ) ` on the left-hand side is redundant.  (The proof was
     shortened by Andrew Salmon, 13-May-2011.)  (The proof was shortened by
     Wolf Lammen, 20-Jan-2013.) $)
  consensus $p |- ( ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) \/ ( ps /\ ch ) ) <->
                      ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) ) $=
    ( wa wn wo id orc adantrr olc adantrl pm2.61ian jaoi impbii ) ABDZAEZCDZFZB
    CDZFRRRSRGASRABRCOQHIPCRBQOJKLMRSHN $.
    $( [20-Jan-2013] $) $( [16-May-2003] $)

  $( Theorem *4.42 of [WhiteheadRussell] p. 119.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) $)
  pm4.42 $p |- ( ph <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps ) ) ) $=
    ( wa wn wo wb dedlema dedlemb pm2.61i ) BAABCABDCEFBAAGBAAHI $.
    $( [21-Jun-2005] $)

  ${
    ninba.1 $e |- ph $.
    $( Miscellaneous inference relating falsehoods. $)
    ninba $p |- ( -. ps -> ( -. ph <-> ( ch /\ ps ) ) ) $=
      ( wn wa niabn bicomd ) BECBFAEABCDGH $.
      $( [31-Mar-1994] $)
  $}

  ${
    prlem1.1 $e |- ( ph -> ( et <-> ch ) ) $.
    prlem1.2 $e |- ( ps -> -. th ) $.
    $( A specialized lemma for set theory (to derive the Axiom of Pairing).
       (The proof was shortened by Andrew Salmon, 13-May-2011.)  (The proof was
       shortened by Wolf Lammen, 5-Jan-2013.) $)
    prlem1 $p |- ( ph -> ( ps ->
                  ( ( ( ps /\ ch ) \/ ( th /\ ta ) ) -> et ) ) ) $=
      ( wa wo wi biimprd adantld pm2.21d adantrd jaao ex ) ABBCIZDEIZJFKARFBSAC
      FBAFCGLMBDFEBDFHNOPQ $.
      $( [5-Jan-2013] $) $( [18-Oct-1995] $)
  $}

  $( A specialized lemma for set theory (to derive the Axiom of Pairing).  (The
     proof was shortened by Andrew Salmon, 13-May-2011.)  (The proof was
     shortened by Wolf Lammen, 9-Dec-2012.) $)
  prlem2 $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <->
              ( ( ph \/ ch ) /\ ( ( ph /\ ps ) \/ ( ch /\ th ) ) ) ) $=
    ( wa wo simpl orim12i pm4.71ri ) ABEZCDEZFACFJAKCABGCDGHI $.
    $( [9-Dec-2012] $) $( [5-Aug-1993] $)

  ${
    oplem1.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    oplem1.2 $e |- ( ph -> ( th \/ ta ) ) $.
    oplem1.3 $e |- ( ps <-> th ) $.
    oplem1.4 $e |- ( ch -> ( th <-> ta ) ) $.
    $( A specialized lemma for set theory (ordered pair theorem).  (The proof
       was shortened by Wolf Lammen, 8-Dec-2012.)
       (The proof was shortened by Mario Carneiro, 2-Feb-2015.) $)
    oplem1 $p |- ( ph -> ps ) $=
      ( wo idd wi ax-1 biimprcd jaoi syl syl6ibr jaod mpd ) ABCJBFABBCABKACDBAD
      EJCDLZGDTEDCMCDEINOPHQRS $.
      $( [2-Feb-2015] $) $( [18-Oct-1995] $)
  $}

  $( Lemma used in construction of real numbers.  (The proof was shortened by
     Andrew Salmon, 26-Jun-2011.) $)
  rnlem $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
  ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) /\ ( ( ph /\ th ) /\ ( ps /\ ch ) ) ) ) $=
    ( wa an4 biimpi an42 biimpri jca adantl impbii ) ABECDEEZACEBDEEZADEBCEEZEM
    NOMNABCDFGOMADBCHZIJOMNOMPGKL $.
    $( [26-Jun-2011] $) $( [4-Sep-1995] $)

  $( A single axiom for Boolean algebra known as DN_1.  See
     ~ http://www-unix.mcs.anl.gov/~~mccune/papers/basax/v12.pdf .
     (Contributed by Jeffrey Hankins, 3-Jul-2009.)  (The proof was shortened by
     Andrew Salmon, 13-May-2011.)  (The proof was shortened by Wolf Lammen,
     6-Jan-2013.) $)
  dn1 $p |- ( -. ( -. ( -. ( ph \/ ps ) \/ ch ) \/
            -. ( ph \/ -. ( -. ch \/ -. ( ch \/ th ) ) ) ) <-> ch ) $=
    ( wo wn wa wi pm2.45 imnan mpbi biorfi orcom ordir 3bitri pm4.45 anor bitri
    orbi2i anbi2i 3bitrri ) CABEFZCEZACEZGZUCACFCDEZFEFZEZGUCFUHFEFCCUBAGZEUICE
    UEUICUBAFHUIFABIUBAJKLCUIMUBACNOUDUHUCCUGACCUFGUGCDPCUFQRSTUCUHQUA $.
    $( [6-Jan-2013] $) $( [22-Jun-2005] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Abbreviated conjunction and disjunction of three wff's
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Extend wff definition to include 3-way disjunction ('or'). $)
  w3o $a wff ( ph \/ ps \/ ch ) $.
  $( Extend wff definition to include 3-way conjunction ('and'). $)
  w3a $a wff ( ph /\ ps /\ ch ) $.

  $( These abbreviations help eliminate parentheses to aid readability. $)

  $( Define disjunction ('or') of 3 wff's.  Definition *2.33 of
     [WhiteheadRussell] p. 105.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ orass . $)
  df-3or $a |- ( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) ) $.

  $( Define conjunction ('and') of 3 wff.s.  Definition *4.34 of
     [WhiteheadRussell] p. 118.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ anass . $)
  df-3an $a |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) ) $.

  $( Associative law for triple disjunction. $)
  3orass $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $=
    ( w3o wo df-3or orass bitri ) ABCDABECEABCEEABCFABCGH $.
    $( [8-Apr-1994] $)

  $( Associative law for triple conjunction. $)
  3anass $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $=
    ( w3a wa df-3an anass bitri ) ABCDABECEABCEEABCFABCGH $.
    $( [8-Apr-1994] $)

  $( Rotation law for triple conjunction. $)
  3anrot $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ch /\ ph ) ) $=
    ( wa w3a ancom 3anass df-3an 3bitr4i ) ABCDZDJADABCEBCAEAJFABCGBCAHI $.
    $( [8-Apr-1994] $)

  $( Rotation law for triple disjunction. $)
  3orrot $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) ) $=
    ( wo w3o orcom 3orass df-3or 3bitr4i ) ABCDZDJADABCEBCAEAJFABCGBCAHI $.
    $( [4-Apr-1995] $)

  $( Commutation law for triple conjunction. $)
  3ancoma $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ph /\ ch ) ) $=
    ( wa w3a ancom anbi1i df-3an 3bitr4i ) ABDZCDBADZCDABCEBACEJKCABFGABCHBACHI
    $.
    $( [21-Apr-1994] $)

  $( Commutation law for triple conjunction. $)
  3ancomb $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ch /\ ps ) ) $=
    ( w3a 3ancoma 3anrot bitri ) ABCDBACDACBDABCEBACFG $.
    $( [21-Apr-1994] $)

  $( Commutation law for triple disjunction.  (Contributed by Scott Fenton,
     20-Apr-2011.) $)
  3orcomb $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ch \/ ps ) ) $=
    ( wo w3o orcom orbi2i 3orass 3bitr4i ) ABCDZDACBDZDABCEACBEJKABCFGABCHACBHI
    $.
    $( [20-Feb-2012] $) $( [20-Apr-2011] $)

  $( Reversal law for triple conjunction. $)
  3anrev $p |- ( ( ph /\ ps /\ ch ) <-> ( ch /\ ps /\ ph ) ) $=
    ( w3a 3ancoma 3anrot bitr4i ) ABCDBACDCBADABCECBAFG $.
    $( [21-Apr-1994] $)

  $( Triple conjunction expressed in terms of triple disjunction.  (Contributed
     by Jeff Hankins, 15-Aug-2009.) $)
  3anor $p |- ( ( ph /\ ps /\ ch ) <-> -. ( -. ph \/ -. ps \/ -. ch ) ) $=
    ( w3a wa wn w3o df-3an wo anor ianor orbi1i xchbinx df-3or xchbinxr bitri )
    ABCDABEZCEZAFZBFZCFZGZFABCHRSTIZUAIZUBRQFZUAIUDQCJUEUCUAABKLMSTUANOP $.
    $( [2-Mar-2011] $) $( [28-Jul-2009] $)

  $( Negated triple conjunction expressed in terms of triple disjunction.
     (Contributed by Jeff Hankins, 15-Aug-2009.)  (The proof was shortened by
     Andrew Salmon, 13-May-2011.) $)
  3ianor $p |- ( -. ( ph /\ ps /\ ch ) <-> ( -. ph \/ -. ps \/ -. ch ) ) $=
    ( wn w3o w3a 3anor con2bii bicomi ) ADBDCDEZABCFZDKJABCGHI $.
    $( [16-May-2011] $) $( [28-Jul-2009] $)

  $( Negated triple disjunction as triple conjunction.  (Contributed by Scott
     Fenton, 19-Apr-2011.) $)
  3ioran $p |- ( -. ( ph \/ ps \/ ch ) <-> ( -. ph /\ -. ps /\ -. ch ) ) $=
    ( wo wn wa w3o w3a ioran anbi1i df-3or xchnxbir df-3an 3bitr4i ) ABDZEZCEZF
    ZAEZBEZFZQFABCGZESTQHPUAQABIJOCDRUBOCIABCKLSTQMN $.
    $( [19-Apr-2011] $)

  $( Triple disjunction in terms of triple conjunction. $)
  3oran $p |- ( ( ph \/ ps \/ ch ) <-> -. ( -. ph /\ -. ps /\ -. ch ) ) $=
    ( wn w3a w3o 3ioran con1bii bicomi ) ADBDCDEZDABCFZKJABCGHI $.
    $( [8-Oct-2012] $)

  $( Simplification of triple conjunction. $)
  3simpa $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ps ) ) $=
    ( w3a wa df-3an simplbi ) ABCDABECABCFG $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  3simpb $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ch ) ) $=
    ( w3a wa 3ancomb 3simpa sylbi ) ABCDACBDACEABCFACBGH $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction.  (The proof was shortened by Andrew
     Salmon, 13-May-2011.) $)
  3simpc $p |- ( ( ph /\ ps /\ ch ) -> ( ps /\ ch ) ) $=
    ( w3a wa 3anrot 3simpa sylbi ) ABCDBCADBCEABCFBCAGH $.
    $( [16-May-2011] $) $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  simp1 $p |- ( ( ph /\ ps /\ ch ) -> ph ) $=
    ( w3a 3simpa simpld ) ABCDABABCEF $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  simp2 $p |- ( ( ph /\ ps /\ ch ) -> ps ) $=
    ( w3a 3simpa simprd ) ABCDABABCEF $.
    $( [21-Apr-1994] $)

  $( Simplification of triple conjunction. $)
  simp3 $p |- ( ( ph /\ ps /\ ch ) -> ch ) $=
    ( w3a 3simpc simprd ) ABCDBCABCEF $.
    $( [21-Apr-1994] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ph ) $=
    ( w3a simp1 adantr ) ABCEADABCFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl2 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ps ) $=
    ( w3a simp2 adantr ) ABCEBDABCFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpl3 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ch ) $=
    ( w3a simp3 adantr ) ABCECDABCFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr1 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ps ) $=
    ( w3a simp1 adantl ) BCDEBABCDFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ch ) $=
    ( w3a simp2 adantl ) BCDECABCDFG $.
    $( [17-Nov-2009] $)

  $( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
  simpr3 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> th ) $=
    ( w3a simp3 adantl ) BCDEDABCDFG $.
    $( [17-Nov-2009] $)

  ${
    3simp1i.1 $e |- ( ph /\ ps /\ ch ) $.
    $( Infer a conjunct from a triple conjunction. $)
    simp1i $p |- ph $=
      ( w3a simp1 ax-mp ) ABCEADABCFG $.
      $( [19-Apr-2005] $)

    $( Infer a conjunct from a triple conjunction. $)
    simp2i $p |- ps $=
      ( w3a simp2 ax-mp ) ABCEBDABCFG $.
      $( [19-Apr-2005] $)

    $( Infer a conjunct from a triple conjunction. $)
    simp3i $p |- ch $=
      ( w3a simp3 ax-mp ) ABCECDABCFG $.
      $( [19-Apr-2005] $)
  $}

  ${
    3simp1d.1 $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
    $( Deduce a conjunct from a triple conjunction. $)
    simp1d $p |- ( ph -> ps ) $=
      ( w3a simp1 syl ) ABCDFBEBCDGH $.
      $( [4-Sep-2005] $)

    $( Deduce a conjunct from a triple conjunction. $)
    simp2d $p |- ( ph -> ch ) $=
      ( w3a simp2 syl ) ABCDFCEBCDGH $.
      $( [4-Sep-2005] $)

    $( Deduce a conjunct from a triple conjunction. $)
    simp3d $p |- ( ph -> th ) $=
      ( w3a simp3 syl ) ABCDFDEBCDGH $.
      $( [4-Sep-2005] $)
  $}

  ${
    3simp1bi.1 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp1bi $p |- ( ph -> ps ) $=
      ( w3a biimpi simp1d ) ABCDABCDFEGH $.
      $( [9-Sep-2011] $) $( [3-Jun-2011] $)

    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp2bi $p |- ( ph -> ch ) $=
      ( w3a biimpi simp2d ) ABCDABCDFEGH $.
      $( [9-Sep-2011] $) $( [3-Jun-2011] $)

    $( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    simp3bi $p |- ( ph -> th ) $=
      ( w3a biimpi simp3d ) ABCDABCDFEGH $.
      $( [9-Sep-2011] $) $( [3-Jun-2011] $)
  $}

  ${
    3adant.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adant1 $p |- ( ( th /\ ph /\ ps ) -> ch ) $=
      ( w3a wa 3simpc syl ) DABFABGCDABHEI $.
      $( [16-Jul-1995] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant2 $p |- ( ( ph /\ th /\ ps ) -> ch ) $=
      ( w3a wa 3simpb syl ) ADBFABGCADBHEI $.
      $( [16-Jul-1995] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( w3a wa 3simpa syl ) ABDFABGCABDHEI $.
      $( [16-Jul-1995] $)
  $}

  ${
    3ad2ant.1 $e |- ( ph -> ch ) $.
    $( Deduction adding conjuncts to an antecedent. $)
    3ad2ant1 $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( adantr 3adant2 ) ADCBACDEFG $.
      $( [21-Apr-2005] $)

    $( Deduction adding conjuncts to an antecedent. $)
    3ad2ant2 $p |- ( ( ps /\ ph /\ th ) -> ch ) $=
      ( adantr 3adant1 ) ADCBACDEFG $.
      $( [21-Apr-2005] $)

    $( Deduction adding conjuncts to an antecedent. $)
    3ad2ant3 $p |- ( ( ps /\ th /\ ph ) -> ch ) $=
      ( adantl 3adant1 ) DACBACDEFG $.
      $( [21-Apr-2005] $)
  $}

  $( Simplification of triple conjunction. $)
  simp1l $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ph ) $=
    ( wa simpl 3ad2ant1 ) ABECADABFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp1r $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ps ) $=
    ( wa simpr 3ad2ant1 ) ABECBDABFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp2l $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ps ) $=
    ( wa simpl 3ad2ant2 ) BCEABDBCFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp2r $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ch ) $=
    ( wa simpr 3ad2ant2 ) BCEACDBCFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp3l $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> ch ) $=
    ( wa simpl 3ad2ant3 ) CDEACBCDFG $.
    $( [9-Nov-2011] $)

  $( Simplification of triple conjunction. $)
  simp3r $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> th ) $=
    ( wa simpr 3ad2ant3 ) CDEADBCDFG $.
    $( [9-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp11 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ph ) $=
    ( w3a simp1 3ad2ant1 ) ABCFDAEABCGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp12 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ps ) $=
    ( w3a simp2 3ad2ant1 ) ABCFDBEABCGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp13 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ch ) $=
    ( w3a simp3 3ad2ant1 ) ABCFDCEABCGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp21 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ps ) $=
    ( w3a simp1 3ad2ant2 ) BCDFABEBCDGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp22 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ch ) $=
    ( w3a simp2 3ad2ant2 ) BCDFACEBCDGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp23 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> th ) $=
    ( w3a simp3 3ad2ant2 ) BCDFADEBCDGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp31 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ch ) $=
    ( w3a simp1 3ad2ant3 ) CDEFACBCDEGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp32 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> th ) $=
    ( w3a simp2 3ad2ant3 ) CDEFADBCDEGH $.
    $( [17-Nov-2011] $)

  $( Simplification of doubly triple conjunction. $)
  simp33 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ta ) $=
    ( w3a simp3 3ad2ant3 ) CDEFAEBCDEGH $.
    $( [17-Nov-2011] $)

  $( Simplification of conjunction. $)
  simpll1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ph ) $=
    ( w3a wa simpl1 adantr ) ABCFDGAEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpll2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ps ) $=
    ( w3a wa simpl2 adantr ) ABCFDGBEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpll3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ch ) $=
    ( w3a wa simpl3 adantr ) ABCFDGCEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simplr1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ph ) $=
    ( w3a wa simpr1 adantr ) DABCFGAEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simplr2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ps ) $=
    ( w3a wa simpr2 adantr ) DABCFGBEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simplr3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ch ) $=
    ( w3a wa simpr3 adantr ) DABCFGCEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprl1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $=
    ( w3a wa simpl1 adantl ) ABCFDGAEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprl2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $=
    ( w3a wa simpl2 adantl ) ABCFDGBEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprl3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $=
    ( w3a wa simpl3 adantl ) ABCFDGCEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprr1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a wa simpr1 adantl ) DABCFGAEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprr2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a wa simpr2 adantl ) DABCFGBEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simprr3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a wa simpr3 adantl ) DABCFGCEDABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl1l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ph ) $=
    ( wa w3a simp1l adantr ) ABFCDGAEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl1r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ps ) $=
    ( wa w3a simp1r adantr ) ABFCDGBEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl2l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ph ) $=
    ( wa w3a simp2l adantr ) CABFDGAECABDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl2r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ps ) $=
    ( wa w3a simp2r adantr ) CABFDGBECABDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl3l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $=
    ( wa w3a simp3l adantr ) CDABFGAECDABHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl3r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $=
    ( wa w3a simp3r adantr ) CDABFGBECDABHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr1l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $=
    ( wa w3a simp1l adantl ) ABFCDGAEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr1r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $=
    ( wa w3a simp1r adantl ) ABFCDGBEABCDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr2l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $=
    ( wa w3a simp2l adantl ) CABFDGAECABDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr2r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $=
    ( wa w3a simp2r adantl ) CABFDGBECABDHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr3l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $=
    ( wa w3a simp3l adantl ) CDABFGAECDABHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr3r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $=
    ( wa w3a simp3r adantl ) CDABFGBECDABHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1ll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ph ) $=
    ( wa simpll 3ad2ant1 ) ABFCFDAEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1lr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ps ) $=
    ( wa simplr 3ad2ant1 ) ABFCFDBEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1rl $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ph ) $=
    ( wa simprl 3ad2ant1 ) CABFFDAECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1rr $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ps ) $=
    ( wa simprr 3ad2ant1 ) CABFFDBECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2ll $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ph ) $=
    ( wa simpll 3ad2ant2 ) ABFCFDAEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2lr $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ps ) $=
    ( wa simplr 3ad2ant2 ) ABFCFDBEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2rl $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $=
    ( wa simprl 3ad2ant2 ) CABFFDAECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2rr $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $=
    ( wa simprr 3ad2ant2 ) CABFFDBECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3ll $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ph ) $=
    ( wa simpll 3ad2ant3 ) ABFCFDAEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3lr $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ps ) $=
    ( wa simplr 3ad2ant3 ) ABFCFDBEABCGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3rl $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ph ) $=
    ( wa simprl 3ad2ant3 ) CABFFDAECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3rr $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ps ) $=
    ( wa simprr 3ad2ant3 ) CABFFDBECABGH $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl11 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ph ) $=
    ( w3a simp11 adantr ) ABCGDEGAFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl12 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ps ) $=
    ( w3a simp12 adantr ) ABCGDEGBFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl13 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ch ) $=
    ( w3a simp13 adantr ) ABCGDEGCFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl21 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ph ) $=
    ( w3a simp21 adantr ) DABCGEGAFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl22 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ps ) $=
    ( w3a simp22 adantr ) DABCGEGBFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl23 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ch ) $=
    ( w3a simp23 adantr ) DABCGEGCFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl31 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $=
    ( w3a simp31 adantr ) DEABCGGAFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl32 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $=
    ( w3a simp32 adantr ) DEABCGGBFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpl33 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $=
    ( w3a simp33 adantr ) DEABCGGCFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr11 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $=
    ( w3a simp11 adantl ) ABCGDEGAFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr12 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $=
    ( w3a simp12 adantl ) ABCGDEGBFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr13 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $=
    ( w3a simp13 adantl ) ABCGDEGCFABCDEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr21 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $=
    ( w3a simp21 adantl ) DABCGEGAFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr22 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $=
    ( w3a simp22 adantl ) DABCGEGBFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr23 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $=
    ( w3a simp23 adantl ) DABCGEGCFDABCEHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr31 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a simp31 adantl ) DEABCGGAFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr32 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a simp32 adantl ) DEABCGGBFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simpr33 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a simp33 adantl ) DEABCGGCFDEABCHI $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1l1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ph ) $=
    ( w3a wa simpl1 3ad2ant1 ) ABCGDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1l2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ps ) $=
    ( w3a wa simpl2 3ad2ant1 ) ABCGDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1l3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ch ) $=
    ( w3a wa simpl3 3ad2ant1 ) ABCGDHECFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1r1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ph ) $=
    ( w3a wa simpr1 3ad2ant1 ) DABCGHEAFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1r2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ps ) $=
    ( w3a wa simpr2 3ad2ant1 ) DABCGHEBFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp1r3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ch ) $=
    ( w3a wa simpr3 3ad2ant1 ) DABCGHECFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2l1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ph ) $=
    ( w3a wa simpl1 3ad2ant2 ) ABCGDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2l2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ps ) $=
    ( w3a wa simpl2 3ad2ant2 ) ABCGDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2l3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ch ) $=
    ( w3a wa simpl3 3ad2ant2 ) ABCGDHECFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2r1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $=
    ( w3a wa simpr1 3ad2ant2 ) DABCGHEAFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2r2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $=
    ( w3a wa simpr2 3ad2ant2 ) DABCGHEBFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp2r3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $=
    ( w3a wa simpr3 3ad2ant2 ) DABCGHECFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3l1 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $=
    ( w3a wa simpl1 3ad2ant3 ) ABCGDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3l2 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $=
    ( w3a wa simpl2 3ad2ant3 ) ABCGDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3l3 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $=
    ( w3a wa simpl3 3ad2ant3 ) ABCGDHECFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3r1 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a wa simpr1 3ad2ant3 ) DABCGHEAFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3r2 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a wa simpr2 3ad2ant3 ) DABCGHEBFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp3r3 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a wa simpr3 3ad2ant3 ) DABCGHECFDABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp11l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ph ) $=
    ( wa w3a simp1l 3ad2ant1 ) ABGCDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp11r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ps ) $=
    ( wa w3a simp1r 3ad2ant1 ) ABGCDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp12l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ph ) $=
    ( wa w3a simp2l 3ad2ant1 ) CABGDHEAFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp12r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ps ) $=
    ( wa w3a simp2r 3ad2ant1 ) CABGDHEBFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp13l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ph ) $=
    ( wa w3a simp3l 3ad2ant1 ) CDABGHEAFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp13r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ps ) $=
    ( wa w3a simp3r 3ad2ant1 ) CDABGHEBFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp21l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ph ) $=
    ( wa w3a simp1l 3ad2ant2 ) ABGCDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp21r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ps ) $=
    ( wa w3a simp1r 3ad2ant2 ) ABGCDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp22l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ph ) $=
    ( wa w3a simp2l 3ad2ant2 ) CABGDHEAFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp22r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ps ) $=
    ( wa w3a simp2r 3ad2ant2 ) CABGDHEBFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp23l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ph ) $=
    ( wa w3a simp3l 3ad2ant2 ) CDABGHEAFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp23r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ps ) $=
    ( wa w3a simp3r 3ad2ant2 ) CDABGHEBFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp31l $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $=
    ( wa w3a simp1l 3ad2ant3 ) ABGCDHEAFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp31r $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $=
    ( wa w3a simp1r 3ad2ant3 ) ABGCDHEBFABCDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp32l $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $=
    ( wa w3a simp2l 3ad2ant3 ) CABGDHEAFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp32r $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $=
    ( wa w3a simp2r 3ad2ant3 ) CABGDHEBFCABDIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp33l $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $=
    ( wa w3a simp3l 3ad2ant3 ) CDABGHEAFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp33r $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $=
    ( wa w3a simp3r 3ad2ant3 ) CDABGHEBFCDABIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp111 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ph ) $=
    ( w3a simp11 3ad2ant1 ) ABCHDEHFAGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp112 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ps ) $=
    ( w3a simp12 3ad2ant1 ) ABCHDEHFBGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp113 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ch ) $=
    ( w3a simp13 3ad2ant1 ) ABCHDEHFCGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp121 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ph ) $=
    ( w3a simp21 3ad2ant1 ) DABCHEHFAGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp122 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ps ) $=
    ( w3a simp22 3ad2ant1 ) DABCHEHFBGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp123 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ch ) $=
    ( w3a simp23 3ad2ant1 ) DABCHEHFCGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp131 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ph ) $=
    ( w3a simp31 3ad2ant1 ) DEABCHHFAGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp132 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ps ) $=
    ( w3a simp32 3ad2ant1 ) DEABCHHFBGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp133 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ch ) $=
    ( w3a simp33 3ad2ant1 ) DEABCHHFCGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp211 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ph ) $=
    ( w3a simp11 3ad2ant2 ) ABCHDEHFAGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp212 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ps ) $=
    ( w3a simp12 3ad2ant2 ) ABCHDEHFBGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp213 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ch ) $=
    ( w3a simp13 3ad2ant2 ) ABCHDEHFCGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp221 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ph ) $=
    ( w3a simp21 3ad2ant2 ) DABCHEHFAGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp222 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ps ) $=
    ( w3a simp22 3ad2ant2 ) DABCHEHFBGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp223 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ch ) $=
    ( w3a simp23 3ad2ant2 ) DABCHEHFCGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp231 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ph ) $=
    ( w3a simp31 3ad2ant2 ) DEABCHHFAGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp232 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ps ) $=
    ( w3a simp32 3ad2ant2 ) DEABCHHFBGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp233 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ch ) $=
    ( w3a simp33 3ad2ant2 ) DEABCHHFCGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp311 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $=
    ( w3a simp11 3ad2ant3 ) ABCHDEHFAGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp312 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $=
    ( w3a simp12 3ad2ant3 ) ABCHDEHFBGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp313 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $=
    ( w3a simp13 3ad2ant3 ) ABCHDEHFCGABCDEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp321 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $=
    ( w3a simp21 3ad2ant3 ) DABCHEHFAGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp322 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $=
    ( w3a simp22 3ad2ant3 ) DABCHEHFBGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp323 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $=
    ( w3a simp23 3ad2ant3 ) DABCHEHFCGDABCEIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp331 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $=
    ( w3a simp31 3ad2ant3 ) DEABCHHFAGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp332 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $=
    ( w3a simp32 3ad2ant3 ) DEABCHHFBGDEABCIJ $.
    $( [9-Mar-2012] $)

  $( Simplification of conjunction. $)
  simp333 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $=
    ( w3a simp33 3ad2ant3 ) DEABCHHFCGDEABCIJ $.
    $( [9-Mar-2012] $)

  ${
    3adantl.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adantl1 $p |- ( ( ( ta /\ ph /\ ps ) /\ ch ) -> th ) $=
      ( w3a wa 3simpc sylan ) EABGABHCDEABIFJ $.
      $( [24-Feb-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantl2 $p |- ( ( ( ph /\ ta /\ ps ) /\ ch ) -> th ) $=
      ( w3a wa 3simpb sylan ) AEBGABHCDAEBIFJ $.
      $( [24-Feb-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantl3 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      ( w3a wa 3simpa sylan ) ABEGABHCDABEIFJ $.
      $( [24-Feb-2005] $)
  $}

  ${
    3adantr.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adantr1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      ( w3a wa 3simpc sylan2 ) EBCGABCHDEBCIFJ $.
      $( [27-Apr-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantr2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( w3a wa 3simpb sylan2 ) BECGABCHDBECIFJ $.
      $( [27-Apr-2005] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adantr3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( w3a wa 3simpa sylan2 ) BCEGABCHDBCEIFJ $.
      $( [27-Apr-2005] $)
  $}

  ${
    3ad2antl.1 $e |- ( ( ph /\ ch ) -> th ) $.
    $( Deduction adding conjuncts to antecedent. $)
    3ad2antl1 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $=
      ( adantlr 3adantl2 ) AECDBACDEFGH $.
      $( [4-Aug-2007] $)

    $( Deduction adding conjuncts to antecedent. $)
    3ad2antl2 $p |- ( ( ( ps /\ ph /\ ta ) /\ ch ) -> th ) $=
      ( adantlr 3adantl1 ) AECDBACDEFGH $.
      $( [4-Aug-2007] $)

    $( Deduction adding conjuncts to antecedent. $)
    3ad2antl3 $p |- ( ( ( ps /\ ta /\ ph ) /\ ch ) -> th ) $=
      ( adantll 3adantl1 ) EACDBACDEFGH $.
      $( [4-Aug-2007] $)

    $( Deduction adding a conjuncts to antecedent. $)
    3ad2antr1 $p |- ( ( ph /\ ( ch /\ ps /\ ta ) ) -> th ) $=
      ( adantrr 3adantr3 ) ACBDEACDBFGH $.
      $( [25-Dec-2007] $)

    $( Deduction adding a conjuncts to antecedent. $)
    3ad2antr2 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( adantrl 3adantr3 ) ABCDEACDBFGH $.
      $( [27-Dec-2007] $)

    $( Deduction adding a conjuncts to antecedent. $)
    3ad2antr3 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( adantrl 3adantr1 ) AECDBACDEFGH $.
      $( [30-Dec-2007] $)
  $}

  ${
    3anibar.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ( ch /\ ta ) ) ) $.
    $( Remove a hypothesis from the second member of a biimplication.
       (Contributed by FL, 22-Jul-2008.) $)
    3anibar $p |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $=
      ( w3a wa simp3 biantrurd bitr4d ) ABCGZDCEHEFLCEABCIJK $.
      $( [2-Mar-2011] $) $( [14-Jul-2008] $)
  $}

  $( Introduction in triple disjunction. $)
  3mix1 $p |- ( ph -> ( ph \/ ps \/ ch ) ) $=
    ( wo w3o orc 3orass sylibr ) AABCDZDABCEAIFABCGH $.
    $( [4-Apr-1995] $)

  $( Introduction in triple disjunction. $)
  3mix2 $p |- ( ph -> ( ps \/ ph \/ ch ) ) $=
    ( w3o 3mix1 3orrot sylibr ) AACBDBACDACBEBACFG $.
    $( [4-Apr-1995] $)

  $( Introduction in triple disjunction. $)
  3mix3 $p |- ( ph -> ( ps \/ ch \/ ph ) ) $=
    ( w3o 3mix1 3orrot sylib ) AABCDBCADABCEABCFG $.
    $( [4-Apr-1995] $)

  ${
    3pm3.2i.1 $e |- ph $.
    3pm3.2i.2 $e |- ps $.
    3pm3.2i.3 $e |- ch $.
    $( Infer conjunction of premises. $)
    3pm3.2i $p |- ( ph /\ ps /\ ch ) $=
      ( w3a wa pm3.2i df-3an mpbir2an ) ABCGABHCABDEIFABCJK $.
      $( [10-Feb-1995] $)
  $}

  ${
    $( ~ pm3.2 for a triple conjunction.  (Contributed by Alan Sare,
       24-Oct-2011.) $)
    pm3.2an3 $p |- ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) ) $=
      ( wa w3a wi pm3.2 ex df-3an bicomi syl8ib ) ABCABDZCDZABCEZABCMFLCGHNMABC
      IJK $.
      $( [24-Oct-2011] $)
  $}

  ${
    3jca.1 $e |- ( ph -> ps ) $.
    3jca.2 $e |- ( ph -> ch ) $.
    3jca.3 $e |- ( ph -> th ) $.
    $( Join consequents with conjunction. $)
    3jca $p |- ( ph -> ( ps /\ ch /\ th ) ) $=
      ( wa w3a jca31 df-3an sylibr ) ABCHDHBCDIABCDEFGJBCDKL $.
      $( [9-Apr-1994] $)
  $}

  ${
    3jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jcad.2 $e |- ( ph -> ( ps -> th ) ) $.
    3jcad.3 $e |- ( ph -> ( ps -> ta ) ) $.
    $( Deduction conjoining the consequents of three implications. $)
    3jcad $p |- ( ph -> ( ps -> ( ch /\ th /\ ta ) ) ) $=
      ( w3a wa imp 3jca ex ) ABCDEIABJCDEABCFKABDGKABEHKLM $.
      $( [25-Sep-2005] $)
  $}

  ${
    mpbir3an.1 $e |- ps $.
    mpbir3an.2 $e |- ch $.
    mpbir3an.3 $e |- th $.
    mpbir3an.4 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    $( Detach a conjunction of truths in a biconditional. $)
    mpbir3an $p |- ph $=
      ( w3a 3pm3.2i mpbir ) ABCDIBCDEFGJHK $.
      $( [9-Jan-2015] $) $( [16-Sep-2011] $)
  $}

  ${
    mpbir3and.1 $e |- ( ph -> ch ) $.
    mpbir3and.2 $e |- ( ph -> th ) $.
    mpbir3and.3 $e |- ( ph -> ta ) $.
    mpbir3and.4 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    $( Detach a conjunction of truths in a biconditional.  (Contributed by
       Mario Carneiro, 11-May-2014.) $)
    mpbir3and $p |- ( ph -> ps ) $=
      ( w3a 3jca mpbird ) ABCDEJACDEFGHKIL $.
      $( [9-Jan-2015] $) $( [11-May-2014] $)
  $}

  ${
    mpbir3anOLD.1 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
    mpbir3anOLD.2 $e |- ps $.
    mpbir3anOLD.3 $e |- ch $.
    mpbir3anOLD.4 $e |- th $.
    $( Obsolete version of ~ mpbir3an as of 9-Jan-2015. $)
    mpbir3anOLD $p |- ph $=
      ( mpbir3an ) ABCDFGHEI $.
      $( [16-Sep-2011] $)
  $}

  ${
    mpbir3andOLD.1 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
    mpbir3andOLD.2 $e |- ( ph -> ch ) $.
    mpbir3andOLD.3 $e |- ( ph -> th ) $.
    mpbir3andOLD.4 $e |- ( ph -> ta ) $.
    $( Obsolete version of ~ mpbir3and as of 9-Jan-2015. $)
    mpbir3andOLD $p |- ( ph -> ps ) $=
      ( mpbir3and ) ABCDEGHIFJ $.
      $( [11-May-2014] $)
  $}

  ${
    syl3anbrc.1 $e |- ( ph -> ps ) $.
    syl3anbrc.2 $e |- ( ph -> ch ) $.
    syl3anbrc.3 $e |- ( ph -> th ) $.
    syl3anbrc.4 $e |- ( ta <-> ( ps /\ ch /\ th ) ) $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 11-May-2014.) $)
    syl3anbrc $p |- ( ph -> ta ) $=
      ( w3a 3jca sylibr ) ABCDJEABCDFGHKIL $.
      $( [11-May-2014] $)
  $}

  ${
    3anim123i.1 $e |- ( ph -> ps ) $.
    3anim123i.2 $e |- ( ch -> th ) $.
    3anim123i.3 $e |- ( ta -> et ) $.
    $( Join antecedents and consequents with conjunction. $)
    3anim123i $p |- ( ( ph /\ ch /\ ta ) -> ( ps /\ th /\ et ) ) $=
      ( w3a 3ad2ant1 3ad2ant2 3ad2ant3 3jca ) ACEJBDFACBEGKCADEHLEAFCIMN $.
      $( [8-Apr-1994] $)
  $}

  ${
    3animi.1 $e |- ( ph -> ps ) $.
    $( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 16-Aug-2009.) $)
    3anim1i $p |- ( ( ph /\ ch /\ th ) -> ( ps /\ ch /\ th ) ) $=
      ( id 3anim123i ) ABCCDDECFDFG $.
      $( [21-Feb-2011] $) $( [16-Aug-2009] $)

    $( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 19-Aug-2009.) $)
    3anim3i $p |- ( ( ch /\ th /\ ph ) -> ( ch /\ th /\ ps ) ) $=
      ( id 3anim123i ) CCDDABCFDFEG $.
      $( [21-Feb-2011] $) $( [16-Aug-2009] $)
  $}

  ${
    bi3.1 $e |- ( ph <-> ps ) $.
    bi3.2 $e |- ( ch <-> th ) $.
    bi3.3 $e |- ( ta <-> et ) $.
    $( Join 3 biconditionals with conjunction. $)
    3anbi123i $p |- ( ( ph /\ ch /\ ta ) <-> ( ps /\ th /\ et ) ) $=
      ( wa w3a anbi12i df-3an 3bitr4i ) ACJZEJBDJZFJACEKBDFKOPEFABCDGHLILACEMBD
      FMN $.
      $( [21-Apr-1994] $)

    $( Join 3 biconditionals with disjunction. $)
    3orbi123i $p |- ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) $=
      ( wo w3o orbi12i df-3or 3bitr4i ) ACJZEJBDJZFJACEKBDFKOPEFABCDGHLILACEMBD
      FMN $.
      $( [17-May-1994] $)
  $}

  ${
    3anbi1i.1 $e |- ( ph <-> ps ) $.
    $( Inference adding two conjuncts to each side of a biconditional. $)
    3anbi1i $p |- ( ( ph /\ ch /\ th ) <-> ( ps /\ ch /\ th ) ) $=
      ( biid 3anbi123i ) ABCCDDECFDFG $.
      $( [8-Sep-2006] $)

    $( Inference adding two conjuncts to each side of a biconditional. $)
    3anbi2i $p |- ( ( ch /\ ph /\ th ) <-> ( ch /\ ps /\ th ) ) $=
      ( biid 3anbi123i ) CCABDDCFEDFG $.
      $( [8-Sep-2006] $)

    $( Inference adding two conjuncts to each side of a biconditional. $)
    3anbi3i $p |- ( ( ch /\ th /\ ph ) <-> ( ch /\ th /\ ps ) ) $=
      ( biid 3anbi123i ) CCDDABCFDFEG $.
      $( [8-Sep-2006] $)
  $}

  ${
    3imp.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( Importation inference. $)
    3imp $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( w3a wa df-3an imp31 sylbi ) ABCFABGCGDABCHABCDEIJ $.
      $( [8-Apr-1994] $)
  $}

  ${
    3impa.1 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
    $( Importation from double to triple conjunction. $)
    3impa $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp31 3imp ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)
  $}

  ${
    3impb.1 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
    $( Importation from double to triple conjunction. $)
    3impb $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp32 3imp ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)
  $}

  ${
    3impia.1 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
    $( Importation to triple conjunction. $)
    3impia $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wi ex 3imp ) ABCDABCDFEGH $.
      $( [13-Jun-2006] $)
  $}

  ${
    3impib.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Importation to triple conjunction. $)
    3impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( exp3a 3imp ) ABCDABCDEFG $.
      $( [13-Jun-2006] $)
  $}

  ${
    3exp.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Exportation inference. $)
    3exp $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $=
      ( w3a pm3.2an3 syl8 ) ABCABCFDABCGEH $.
      $( [30-May-1994] $)

    $( Exportation from triple to double conjunction. $)
    3expa $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $=
      ( 3exp imp31 ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)

    $( Exportation from triple to double conjunction. $)
    3expb $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $=
      ( 3exp imp32 ) ABCDABCDEFG $.
      $( [20-Aug-1995] $)

    $( Exportation from triple conjunction. $)
    3expia $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $=
      ( wi 3exp imp ) ABCDFABCDEGH $.
      $( [19-May-2007] $)

    $( Exportation from triple conjunction. $)
    3expib $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $=
      ( 3exp imp3a ) ABCDABCDEFG $.
      $( [19-May-2007] $)

    $( Commutation in antecedent.  Swap 1st and 3rd.  (The proof was shortened
       by Andrew Salmon, 13-May-2011.) $)
    3com12 $p |- ( ( ps /\ ph /\ ch ) -> th ) $=
      ( w3a 3ancoma sylbi ) BACFABCFDBACGEH $.
      $( [16-May-2011] $) $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Swap 1st and 3rd. $)
    3com13 $p |- ( ( ch /\ ps /\ ph ) -> th ) $=
      ( w3a 3anrev sylbi ) CBAFABCFDCBAGEH $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Swap 2nd and 3rd. $)
    3com23 $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      ( 3exp com23 3imp ) ACBDABCDABCDEFGH $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Rotate left. $)
    3coml $p |- ( ( ps /\ ch /\ ph ) -> th ) $=
      ( 3com23 3com13 ) ACBDABCDEFG $.
      $( [28-Jan-1996] $)

    $( Commutation in antecedent.  Rotate right. $)
    3comr $p |- ( ( ch /\ ph /\ ps ) -> th ) $=
      ( 3coml ) BCADABCDEFF $.
      $( [28-Jan-1996] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $=
      ( 3expb 3adantr1 ) ABCDEABCDFGH $.
      $( [16-Feb-2008] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $=
      ( 3expb 3adantr2 ) ABCDEABCDFGH $.
      $( [17-Feb-2008] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $=
      ( 3expb 3adantr3 ) ABCDEABCDFGH $.
      $( [18-Feb-2008] $)
  $}

  ${
    3an1rs.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Swap conjuncts. $)
    3an1rs $p |- ( ( ( ph /\ ps /\ th ) /\ ch ) -> ta ) $=
      ( w3a wi ex 3exp com34 3imp imp ) ABDGCEABDCEHABCDEABCDEHABCGDEFIJKLM $.
      $( [16-Dec-2007] $)
  $}

  ${
    3imp1.1 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
    $( Importation to left triple conjunction. $)
    3imp1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      ( w3a wi 3imp imp ) ABCGDEABCDEHFIJ $.
      $( [24-Feb-2005] $)

    $( Importation deduction for triple conjunction. $)
    3impd $p |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $=
      ( w3a wi com4l 3imp com12 ) BCDGAEBCDAEHABCDEFIJK $.
      $( [26-Oct-2006] $)

    $( Importation to right triple conjunction. $)
    3imp2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      ( w3a 3impd imp ) ABCDGEABCDEFHI $.
      $( [26-Oct-2006] $)
  $}

  ${
    3exp1.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( Exportation from left triple conjunction. $)
    3exp1 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi w3a ex 3exp ) ABCDEGABCHDEFIJ $.
      $( [24-Feb-2005] $)
  $}

  ${
    3expd.1 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( Exportation deduction for triple conjunction. $)
    3expd $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( wi w3a com12 3exp com4r ) BCDAEBCDAEGABCDHEFIJK $.
      $( [26-Oct-2006] $)
  $}

  ${
    3exp2.1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( Exportation from right triple conjunction. $)
    3exp2 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $=
      ( w3a ex 3expd ) ABCDEABCDGEFHI $.
      $( [26-Oct-2006] $)
  $}

  ${
    exp5o.1 $e |- ( ( ph /\ ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp5o $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi w3a exp3a 3exp ) ABCDEFHHABCIDEFGJK $.
      $( [8-Jul-2009] $)
  $}

  ${
    exp516.1 $e |- ( ( ( ph /\ ( ps /\ ch /\ th ) ) /\ ta ) -> et ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp516 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( wi w3a exp31 3expd ) ABCDEFHABCDIEFGJK $.
      $( [8-Jul-2009] $)
  $}

  ${
    exp520.1 $e |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
    $( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
    exp520 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $=
      ( w3a wa ex exp5o ) ABCDEFABCHDEIFGJK $.
      $( [8-Jul-2009] $)
  $}

  ${
    3adant1l.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Deduction adding a conjunct to antecedent. $)
    3adant1l $p |- ( ( ( ta /\ ph ) /\ ps /\ ch ) -> th ) $=
      ( wa 3expb adantll 3impb ) EAGBCDABCGDEABCDFHIJ $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant1r $p |- ( ( ( ph /\ ta ) /\ ps /\ ch ) -> th ) $=
      ( wa 3expb adantlr 3impb ) AEGBCDABCGDEABCDFHIJ $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant2l $p |- ( ( ph /\ ( ta /\ ps ) /\ ch ) -> th ) $=
      ( wa 3com12 3adant1l ) EBGACDBACDEABCDFHIH $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant2r $p |- ( ( ph /\ ( ps /\ ta ) /\ ch ) -> th ) $=
      ( wa 3com12 3adant1r ) BEGACDBACDEABCDFHIH $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3l $p |- ( ( ph /\ ps /\ ( ta /\ ch ) ) -> th ) $=
      ( wa 3com13 3adant1l ) ECGBADCBADEABCDFHIH $.
      $( [8-Jan-2006] $)

    $( Deduction adding a conjunct to antecedent. $)
    3adant3r $p |- ( ( ph /\ ps /\ ( ch /\ ta ) ) -> th ) $=
      ( wa 3com13 3adant1r ) CEGBADCBADEABCDFHIH $.
      $( [8-Jan-2006] $)
  $}

  ${
    sylXanc.1 $e |- ( ph -> ps ) $.
    sylXanc.2 $e |- ( ph -> ch ) $.
    sylXanc.3 $e |- ( ph -> th ) $.
    ${
      syl12anc.4 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
      syl12anc $p |- ( ph -> ta ) $=
        ( wa jca32 syl ) ABCDJJEABCDFGHKIL $.
        $( [1-Aug-2009] $)
    $}

    ${
      syl21anc.4 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
      $( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
      syl21anc $p |- ( ph -> ta ) $=
        ( wa jca31 syl ) ABCJDJEABCDFGHKIL $.
        $( [1-Aug-2009] $)
    $}

    ${
      syl111anc.4 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
      $( Syllogism combined with contraction. $)
      syl3anc $p |- ( ph -> ta ) $=
        ( w3a 3jca syl ) ABCDJEABCDFGHKIL $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.4 $e |- ( ph -> ta ) $.
    ${
      syl22anc.5 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl22anc $p |- ( ph -> et ) $=
        ( wa jca syl12anc ) ABCLDEFABCGHMIJKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl13anc.5 $e |- ( ( ps /\ ( ch /\ th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl13anc $p |- ( ph -> et ) $=
        ( w3a 3jca syl2anc ) ABCDELFGACDEHIJMKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl31anc.5 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl31anc $p |- ( ph -> et ) $=
        ( w3a 3jca syl2anc ) ABCDLEFABCDGHIMJKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl112anc.5 $e |- ( ( ps /\ ch /\ ( th /\ ta ) ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl112anc $p |- ( ph -> et ) $=
        ( wa jca syl3anc ) ABCDELFGHADEIJMKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl121anc.5 $e |- ( ( ps /\ ( ch /\ th ) /\ ta ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl121anc $p |- ( ph -> et ) $=
        ( wa jca syl3anc ) ABCDLEFGACDHIMJKN $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl211anc.5 $e |- ( ( ( ps /\ ch ) /\ th /\ ta ) -> et ) $.
      $( Syllogism combined with contraction. $)
      syl211anc $p |- ( ph -> et ) $=
        ( wa jca syl3anc ) ABCLDEFABCGHMIJKN $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.5 $e |- ( ph -> et ) $.
    ${
      syl23anc.6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl23anc $p |- ( ph -> ze ) $=
        ( wa jca syl13anc ) ABCNDEFGABCHIOJKLMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl32anc.6 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl32anc $p |- ( ph -> ze ) $=
        ( wa jca syl31anc ) ABCDEFNGHIJAEFKLOMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl122anc.6 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl122anc $p |- ( ph -> ze ) $=
        ( wa jca syl121anc ) ABCDEFNGHIJAEFKLOMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl212anc.6 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl212anc $p |- ( ph -> ze ) $=
        ( wa jca syl211anc ) ABCDEFNGHIJAEFKLOMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl221anc.6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ et ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl221anc $p |- ( ph -> ze ) $=
        ( wa jca syl211anc ) ABCDENFGHIADEJKOLMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl113anc.6 $e |- ( ( ps /\ ch /\ ( th /\ ta /\ et ) ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl113anc $p |- ( ph -> ze ) $=
        ( w3a 3jca syl3anc ) ABCDEFNGHIADEFJKLOMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl131anc.6 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ et ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl131anc $p |- ( ph -> ze ) $=
        ( w3a 3jca syl3anc ) ABCDENFGHACDEIJKOLMP $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl311anc.6 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ et ) -> ze ) $.
      $( Syllogism combined with contraction. $)
      syl311anc $p |- ( ph -> ze ) $=
        ( w3a 3jca syl3anc ) ABCDNEFGABCDHIJOKLMP $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.6 $e |- ( ph -> ze ) $.
    ${
      syl33anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl33anc $p |- ( ph -> si ) $=
        ( w3a 3jca syl13anc ) ABCDPEFGHABCDIJKQLMNOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl222anc.7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl222anc $p |- ( ph -> si ) $=
        ( wa jca syl221anc ) ABCDEFGPHIJKLAFGMNQOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl123anc.7 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl123anc $p |- ( ph -> si ) $=
        ( wa jca syl113anc ) ABCDPEFGHIACDJKQLMNOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl132anc.7 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl132anc $p |- ( ph -> si ) $=
        ( wa jca syl131anc ) ABCDEFGPHIJKLAFGMNQOR $.
        $( [11-Jul-2012] $)
    $}

    ${
      syl213anc.7 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl213anc $p |- ( ph -> si ) $=
        ( wa jca syl113anc ) ABCPDEFGHABCIJQKLMNOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl231anc.7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ze )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl231anc $p |- ( ph -> si ) $=
        ( wa jca syl131anc ) ABCPDEFGHABCIJQKLMNOR $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl312anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze ) )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl312anc $p |- ( ph -> si ) $=
        ( wa jca syl311anc ) ABCDEFGPHIJKLAFGMNQOR $.
        $( [11-Jul-2012] $)
    $}

    ${
      syl321anc.7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ze )
           -> si ) $.
      $( Syllogism combined with contraction. $)
      syl321anc $p |- ( ph -> si ) $=
        ( wa jca syl311anc ) ABCDEFPGHIJKAEFLMQNOR $.
        $( [11-Jul-2012] $)
    $}

    sylXanc.7 $e |- ( ph -> si ) $.
    ${
      syl133anc.8 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze /\ si ) )
           -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl133anc $p |- ( ph -> rh ) $=
        ( w3a 3jca syl131anc ) ABCDEFGHRIJKLMAFGHNOPSQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl313anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze /\ si ) )
           -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl313anc $p |- ( ph -> rh ) $=
        ( w3a 3jca syl311anc ) ABCDEFGHRIJKLMAFGHNOPSQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl331anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ si )
           -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl331anc $p |- ( ph -> rh ) $=
        ( w3a 3jca syl311anc ) ABCDEFGRHIJKLAEFGMNOSPQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl223anc.8 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl223anc $p |- ( ph -> rh ) $=
        ( wa jca syl213anc ) ABCDERFGHIJKADELMSNOPQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl232anc.8 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl232anc $p |- ( ph -> rh ) $=
        ( wa jca syl231anc ) ABCDEFGHRIJKLMNAGHOPSQT $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl322anc.8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si )
          ) -> rh ) $.
      $( Syllogism combined with contraction. $)
      syl322anc $p |- ( ph -> rh ) $=
        ( wa jca syl321anc ) ABCDEFGHRIJKLMNAGHOPSQT $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.8 $e |- ( ph -> rh ) $.
    ${
      syl233anc.9 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction. $)
      syl233anc $p |- ( ph -> mu ) $=
        ( wa jca syl133anc ) ABCTDEFGHIJABCKLUAMNOPQRSUB $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl323anc.9 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction. $)
      syl323anc $p |- ( ph -> mu ) $=
        ( wa jca syl313anc ) ABCDEFTGHIJKLMAEFNOUAPQRSUB $.
        $( [11-Mar-2012] $)
    $}

    ${
      syl332anc.9 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\
          rh ) ) -> mu ) $.
      $( Syllogism combined with contraction. $)
      syl332anc $p |- ( ph -> mu ) $=
        ( wa jca syl331anc ) ABCDEFGHITJKLMNOPAHIQRUASUB $.
        $( [11-Mar-2012] $)
    $}

    sylXanc.9 $e |- ( ph -> mu ) $.
    ${
      syl333anc.10 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze )
          /\ ( si /\ rh /\ mu ) ) -> la ) $.
      $( A syllogism inference combined with contraction. $)
      syl333anc $p |- ( ph -> la ) $=
        ( w3a 3jca syl331anc ) ABCDEFGHIJUBKLMNOPQAHIJRSTUCUAUD $.
        $( [10-Mar-2012] $)
    $}
  $}

  ${
    syl3an1.1 $e |- ( ph -> ps ) $.
    syl3an1.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an1 $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( w3a 3anim1i syl ) ACDHBCDHEABCDFIGJ $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an2.1 $e |- ( ph -> ch ) $.
    syl3an2.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an2 $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      ( wi 3exp syl5 3imp ) BADEACBDEHFBCDEGIJK $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an3.1 $e |- ( ph -> th ) $.
    syl3an3.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an3 $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      ( 3exp syl7 3imp ) BCAEADBCEFBCDEGHIJ $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an1b.1 $e |- ( ph <-> ps ) $.
    syl3an1b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an1b $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( biimpi syl3an1 ) ABCDEABFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an2b.1 $e |- ( ph <-> ch ) $.
    syl3an2b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an2b $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      ( biimpi syl3an2 ) ABCDEACFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an3b.1 $e |- ( ph <-> th ) $.
    syl3an3b.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an3b $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      ( biimpi syl3an3 ) ABCDEADFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an1br.1 $e |- ( ps <-> ph ) $.
    syl3an1br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an1br $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( biimpri syl3an1 ) ABCDEBAFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an2br.1 $e |- ( ch <-> ph ) $.
    syl3an2br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an2br $p |- ( ( ps /\ ph /\ th ) -> ta ) $=
      ( biimpri syl3an2 ) ABCDECAFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an3br.1 $e |- ( th <-> ph ) $.
    syl3an3br.2 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syl3an3br $p |- ( ( ps /\ ch /\ ph ) -> ta ) $=
      ( biimpri syl3an3 ) ABCDEDAFHGI $.
      $( [22-Aug-1995] $)
  $}

  ${
    syl3an.1 $e |- ( ph -> ps ) $.
    syl3an.2 $e |- ( ch -> th ) $.
    syl3an.3 $e |- ( ta -> et ) $.
    syl3an.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference. $)
    syl3an $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( w3a 3anim123i syl ) ACELBDFLGABCDEFHIJMKN $.
      $( [13-May-2004] $)
  $}

  ${
    syl3anb.1 $e |- ( ph <-> ps ) $.
    syl3anb.2 $e |- ( ch <-> th ) $.
    syl3anb.3 $e |- ( ta <-> et ) $.
    syl3anb.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference. $)
    syl3anb $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( w3a 3anbi123i sylbi ) ACELBDFLGABCDEFHIJMKN $.
      $( [15-Oct-2005] $)
  $}

  ${
    syl3anbr.1 $e |- ( ps <-> ph ) $.
    syl3anbr.2 $e |- ( th <-> ch ) $.
    syl3anbr.3 $e |- ( et <-> ta ) $.
    syl3anbr.4 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
    $( A triple syllogism inference. $)
    syl3anbr $p |- ( ( ph /\ ch /\ ta ) -> ze ) $=
      ( bicomi syl3anb ) ABCDEFGBAHLDCILFEJLKM $.
      $( [29-Dec-2011] $)
  $}

  ${
    syld3an3.1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    syld3an3.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syld3an3 $p |- ( ( ph /\ ps /\ ch ) -> ta ) $=
      ( w3a simp1 simp2 syl3anc ) ABCHABDEABCIABCJFGK $.
      $( [20-May-2007] $)
  $}

  ${
    syld3an1.1 $e |- ( ( ch /\ ps /\ th ) -> ph ) $.
    syld3an1.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syld3an1 $p |- ( ( ch /\ ps /\ th ) -> ta ) $=
      ( 3com13 syld3an3 ) DBCEDBCAECBDAFHABDEGHIH $.
      $( [7-Jul-2008] $)
  $}

  ${
    syld3an2.1 $e |- ( ( ph /\ ch /\ th ) -> ps ) $.
    syld3an2.2 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
    $( A syllogism inference. $)
    syld3an2 $p |- ( ( ph /\ ch /\ th ) -> ta ) $=
      ( 3com23 syld3an3 ) ADCEADCBEACDBFHABDEGHIH $.
      $( [20-May-2007] $)
  $}

  ${
    syl3anl1.1 $e |- ( ph -> ps ) $.
    syl3anl1.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference. $)
    syl3anl1 $p |- ( ( ( ph /\ ch /\ th ) /\ ta ) -> et ) $=
      ( w3a 3anim1i sylan ) ACDIBCDIEFABCDGJHK $.
      $( [24-Feb-2005] $)
  $}

  ${
    syl3anl2.1 $e |- ( ph -> ch ) $.
    syl3anl2.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference. $)
    syl3anl2 $p |- ( ( ( ps /\ ph /\ th ) /\ ta ) -> et ) $=
      ( w3a wi ex syl3an2 imp ) BADIEFABCDEFJGBCDIEFHKLM $.
      $( [24-Feb-2005] $)
  $}

  ${
    syl3anl3.1 $e |- ( ph -> th ) $.
    syl3anl3.2 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
    $( A syllogism inference. $)
    syl3anl3 $p |- ( ( ( ps /\ ch /\ ph ) /\ ta ) -> et ) $=
      ( w3a 3anim3i sylan ) BCAIBCDIEFADBCGJHK $.
      $( [24-Feb-2005] $)
  $}

  ${
    syl3anl.1 $e |- ( ph -> ps ) $.
    syl3anl.2 $e |- ( ch -> th ) $.
    syl3anl.3 $e |- ( ta -> et ) $.
    syl3anl.4 $e |- ( ( ( ps /\ th /\ et ) /\ ze ) -> si ) $.
    $( A triple syllogism inference. $)
    syl3anl $p |- ( ( ( ph /\ ch /\ ta ) /\ ze ) -> si ) $=
      ( w3a 3anim123i sylan ) ACEMBDFMGHABCDEFIJKNLO $.
      $( [24-Dec-2006] $)
  $}

  ${
    syl3anr1.1 $e |- ( ph -> ps ) $.
    syl3anr1.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference. $)
    syl3anr1 $p |- ( ( ch /\ ( ph /\ th /\ ta ) ) -> et ) $=
      ( w3a 3anim1i sylan2 ) ADEICBDEIFABDEGJHK $.
      $( [31-Jul-2007] $)
  $}

  ${
    syl3anr2.1 $e |- ( ph -> th ) $.
    syl3anr2.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference. $)
    syl3anr2 $p |- ( ( ch /\ ( ps /\ ph /\ ta ) ) -> et ) $=
      ( w3a ancoms syl3anl2 ) BAEICFABDECFGCBDEIFHJKJ $.
      $( [1-Aug-2007] $)
  $}

  ${
    syl3anr3.1 $e |- ( ph -> ta ) $.
    syl3anr3.2 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
    $( A syllogism inference. $)
    syl3anr3 $p |- ( ( ch /\ ( ps /\ th /\ ph ) ) -> et ) $=
      ( w3a 3anim3i sylan2 ) BDAICBDEIFAEBDGJHK $.
      $( [23-Aug-2007] $)
  $}

  ${
    3impdi.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th ) $.
    $( Importation inference (undistribute conjunction). $)
    3impdi $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( anandis 3impb ) ABCDABCDEFG $.
      $( [14-Aug-1995] $)
  $}

  ${
    3impdir.1 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ ps ) ) -> th ) $.
    $( Importation inference (undistribute conjunction). $)
    3impdir $p |- ( ( ph /\ ch /\ ps ) -> th ) $=
      ( anandirs 3impa ) ACBDACBDEFG $.
      $( [20-Aug-1995] $)
  $}

  ${
    3anidm12.1 $e |- ( ( ph /\ ph /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction. $)
    3anidm12 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3expib anabsi5 ) ABCAABCDEF $.
      $( [7-Mar-2008] $)
  $}

  ${
    3anidm13.1 $e |- ( ( ph /\ ps /\ ph ) -> ch ) $.
    $( Inference from idempotent law for conjunction. $)
    3anidm13 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3com23 3anidm12 ) ABCABACDEF $.
      $( [7-Mar-2008] $)
  $}

  ${
    3anidm23.1 $e |- ( ( ph /\ ps /\ ps ) -> ch ) $.
    $( Inference from idempotent law for conjunction. $)
    3anidm23 $p |- ( ( ph /\ ps ) -> ch ) $=
      ( 3expa anabss3 ) ABCABBCDEF $.
      $( [1-Feb-2007] $)
  $}

  ${
    3ori.1 $e |- ( ph \/ ps \/ ch ) $.
    $( Infer implication from triple disjunction. $)
    3ori $p |- ( ( -. ph /\ -. ps ) -> ch ) $=
      ( wn wa wo ioran w3o df-3or mpbi ori sylbir ) AEBEFABGZECABHNCABCINCGDABC
      JKLM $.
      $( [26-Sep-2006] $)
  $}

  $( Disjunction of 3 antecedents. $)
  3jao $p |- ( ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ->
              ( ( ph \/ ch \/ th ) -> ps ) ) $=
    ( w3o wo wi w3a df-3or jao syl6 3imp syl5bi ) ACDEACFZDFZABGZCBGZDBGZHBACDI
    PQROBGZPQNBGRSGABCJNBDJKLM $.
    $( [8-Apr-1994] $)

  $( Disjunction of 3 antecedents. $)
  3jaob $p |- ( ( ( ph \/ ch \/ th ) -> ps ) <->
              ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ) $=
    ( w3o wi w3a 3mix1 imim1i 3mix2 3mix3 3jca 3jao impbii ) ACDEZBFZABFZCBFZDB
    FZGPQRSAOBACDHICOBCADJIDOBDACKILABCDMN $.
    $( [13-Sep-2011] $)

  ${
    3jaoi.1 $e |- ( ph -> ps ) $.
    3jaoi.2 $e |- ( ch -> ps ) $.
    3jaoi.3 $e |- ( th -> ps ) $.
    $( Disjunction of 3 antecedents (inference). $)
    3jaoi $p |- ( ( ph \/ ch \/ th ) -> ps ) $=
      ( wi w3a w3o 3pm3.2i 3jao ax-mp ) ABHZCBHZDBHZIACDJBHNOPEFGKABCDLM $.
      $( [12-Sep-1995] $)
  $}

  ${
    3jaod.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jaod.2 $e |- ( ph -> ( th -> ch ) ) $.
    3jaod.3 $e |- ( ph -> ( ta -> ch ) ) $.
    $( Disjunction of 3 antecedents (deduction). $)
    3jaod $p |- ( ph -> ( ( ps \/ th \/ ta ) -> ch ) ) $=
      ( wi w3o 3jao syl3anc ) ABCIDCIECIBDEJCIFGHBCDEKL $.
      $( [14-Oct-2005] $)
  $}

  ${
    3jaoian.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaoian.2 $e |- ( ( th /\ ps ) -> ch ) $.
    3jaoian.3 $e |- ( ( ta /\ ps ) -> ch ) $.
    $( Disjunction of 3 antecedents (inference). $)
    3jaoian $p |- ( ( ( ph \/ th \/ ta ) /\ ps ) -> ch ) $=
      ( w3o wi ex 3jaoi imp ) ADEIBCABCJDEABCFKDBCGKEBCHKLM $.
      $( [14-Oct-2005] $)
  $}

  ${
    3jaodan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    3jaodan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    3jaodan.3 $e |- ( ( ph /\ ta ) -> ch ) $.
    $( Disjunction of 3 antecedents (deduction). $)
    3jaodan $p |- ( ( ph /\ ( ps \/ th \/ ta ) ) -> ch ) $=
      ( w3o ex 3jaod imp ) ABDEICABCDEABCFJADCGJAECHJKL $.
      $( [14-Oct-2005] $)
  $}

  ${
    3jaao.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3jaao.2 $e |- ( th -> ( ta -> ch ) ) $.
    3jaao.3 $e |- ( et -> ( ze -> ch ) ) $.
    $( Inference conjoining and disjoining the antecedents of three
       implications.  (Contributed by Jeff Hankins, 15-Aug-2009.)  (The proof
       was shortened by Andrew Salmon, 13-May-2011.) $)
    3jaao $p |- ( ( ph /\ th /\ et ) -> ( ( ps \/ ta \/ ze ) -> ch ) ) $=
      ( w3a wi 3ad2ant1 3ad2ant2 3ad2ant3 3jaod ) ADFKBCEGADBCLFHMDAECLFINFAGCL
      DJOP $.
      $( [16-May-2011] $) $( [3-Aug-2009] $)
  $}

  ${
    syl3an9b.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    syl3an9b.2 $e |- ( th -> ( ch <-> ta ) ) $.
    syl3an9b.3 $e |- ( et -> ( ta <-> ze ) ) $.
    $( Nested syllogism inference conjoining 3 dissimilar antecedents. $)
    syl3an9b $p |- ( ( ph /\ th /\ et ) -> ( ps <-> ze ) ) $=
      ( wb wa sylan9bb 3impa ) ADFBGKADLBEFGABCDEHIMJMN $.
      $( [1-May-1995] $)
  $}

  ${
    bi3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bi3d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    bi3d.3 $e |- ( ph -> ( et <-> ze ) ) $.
    $( Deduction joining 3 equivalences to form equivalence of disjunctions. $)
    3orbi123d $p |- ( ph -> ( ( ps \/ th \/ et ) <-> ( ch \/ ta \/ ze ) ) ) $=
      ( wo w3o orbi12d df-3or 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [20-Apr-1994] $)

    $( Deduction joining 3 equivalences to form equivalence of conjunctions. $)
    3anbi123d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ ze ) ) ) $=
      ( wa w3a anbi12d df-3an 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [22-Apr-1994] $)
  $}

  ${
    3anbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    3anbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction conjoining and adding a conjunct to equivalences. $)
    3anbi12d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ et ) ) ) $=
      ( biidd 3anbi123d ) ABCDEFFGHAFIJ $.
      $( [8-Sep-2006] $)

    $( Deduction conjoining and adding a conjunct to equivalences. $)
    3anbi13d $p |- ( ph -> ( ( ps /\ et /\ th ) <-> ( ch /\ et /\ ta ) ) ) $=
      ( biidd 3anbi123d ) ABCFFDEGAFIHJ $.
      $( [8-Sep-2006] $)

    $( Deduction conjoining and adding a conjunct to equivalences. $)
    3anbi23d $p |- ( ph -> ( ( et /\ ps /\ th ) <-> ( et /\ ch /\ ta ) ) ) $=
      ( biidd 3anbi123d ) AFFBCDEAFIGHJ $.
      $( [8-Sep-2006] $)
  $}

  ${
    3anbi1d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction adding conjuncts to an equivalence. $)
    3anbi1d $p |- ( ph -> ( ( ps /\ th /\ ta ) <-> ( ch /\ th /\ ta ) ) ) $=
      ( biidd 3anbi12d ) ABCDDEFADGH $.
      $( [8-Sep-2006] $)

    $( Deduction adding conjuncts to an equivalence. $)
    3anbi2d $p |- ( ph -> ( ( th /\ ps /\ ta ) <-> ( th /\ ch /\ ta ) ) ) $=
      ( biidd 3anbi12d ) ADDBCEADGFH $.
      $( [8-Sep-2006] $)

    $( Deduction adding conjuncts to an equivalence. $)
    3anbi3d $p |- ( ph -> ( ( th /\ ta /\ ps ) <-> ( th /\ ta /\ ch ) ) ) $=
      ( biidd 3anbi13d ) ADDBCEADGFH $.
      $( [8-Sep-2006] $)
  $}

  ${
    3anim123d.1 $e |- ( ph -> ( ps -> ch ) ) $.
    3anim123d.2 $e |- ( ph -> ( th -> ta ) ) $.
    3anim123d.3 $e |- ( ph -> ( et -> ze ) ) $.
    $( Deduction joining 3 implications to form implication of conjunctions. $)
    3anim123d $p |- ( ph -> ( ( ps /\ th /\ et ) -> ( ch /\ ta /\ ze ) ) ) $=
      ( wa w3a anim12d df-3an 3imtr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [24-Feb-2005] $)

    $( Deduction joining 3 implications to form implication of disjunctions. $)
    3orim123d $p |- ( ph -> ( ( ps \/ th \/ et ) -> ( ch \/ ta \/ ze ) ) ) $=
      ( wo w3o orim12d df-3or 3imtr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJMBDF
      NCEGNO $.
      $( [4-Apr-1997] $)
  $}

  $( Rearrangement of 6 conjuncts. $)
  an6 $p |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta /\ et ) ) <->
              ( ( ph /\ th ) /\ ( ps /\ ta ) /\ ( ch /\ et ) ) ) $=
    ( w3a wa df-3an anbi12i an4 anbi1i 3bitri bitr4i ) ABCGZDEFGZHZADHZBEHZHZCF
    HZHZRSUAGQABHZCHZDEHZFHZHUCUEHZUAHUBOUDPUFABCIDEFIJUCCUEFKUGTUAABDEKLMRSUAI
    N $.
    $( [13-Mar-1995] $)

  $( Analog of ~ an4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.)  (The proof was shortened by Andrew Salmon, 25-May-2011.) $)
  3an6 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) /\ ( ta /\ et ) ) <->
                ( ( ph /\ ch /\ ta ) /\ ( ps /\ th /\ et ) ) ) $=
    ( w3a wa an6 bicomi ) ACEGBDFGHABHCDHEFHGACEBDFIJ $.
    $( [25-May-2011] $) $( [16-Mar-2011] $)

  $( Analog of ~ or4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.) $)
  3or6 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) \/ ( ta \/ et ) ) <->
                ( ( ph \/ ch \/ ta ) \/ ( ps \/ th \/ et ) ) ) $=
    ( wo w3o or4 orbi1i bitr2i df-3or orbi12i 3bitr4i ) ABGZCDGZGZEFGZGZACGZEGZ
    BDGZFGZGZOPRHACEHZBDFHZGUDTUBGZRGSTEUBFIUGQRACBDIJKOPRLUEUAUFUCACELBDFLMN
    $.
    $( [20-Mar-2011] $)

  ${
    mp3an1.1 $e |- ph $.
    mp3an1.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an1 $p |- ( ( ps /\ ch ) -> th ) $=
      ( wa 3expb mpan ) ABCGDEABCDFHI $.
      $( [21-Nov-1994] $)
  $}

  ${
    mp3an2.1 $e |- ps $.
    mp3an2.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an2 $p |- ( ( ph /\ ch ) -> th ) $=
      ( 3expa mpanl2 ) ABCDEABCDFGH $.
      $( [21-Nov-1994] $)
  $}

  ${
    mp3an3.1 $e |- ch $.
    mp3an3.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa 3expia mpi ) ABGCDEABCDFHI $.
      $( [21-Nov-1994] $)
  $}

  ${
    mp3an12.1 $e |- ph $.
    mp3an12.2 $e |- ps $.
    mp3an12.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an12 $p |- ( ch -> th ) $=
      ( mp3an1 mpan ) BCDFABCDEGHI $.
      $( [13-Jul-2005] $)
  $}

  ${
    mp3an13.1 $e |- ph $.
    mp3an13.2 $e |- ch $.
    mp3an13.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an13 $p |- ( ps -> th ) $=
      ( mp3an3 mpan ) ABDEABCDFGHI $.
      $( [14-Jul-2005] $)
  $}

  ${
    mp3an23.1 $e |- ps $.
    mp3an23.2 $e |- ch $.
    mp3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an23 $p |- ( ph -> th ) $=
      ( mp3an3 mpan2 ) ABDEABCDFGHI $.
      $( [14-Jul-2005] $)
  $}

  ${
    mp3an1i.1 $e |- ps $.
    mp3an1i.2 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
    $( An inference based on modus ponens. $)
    mp3an1i $p |- ( ph -> ( ( ch /\ th ) -> ta ) ) $=
      ( wa wi w3a com12 mp3an1 ) CDHAEBCDAEIFABCDJEGKLK $.
      $( [5-Jul-2005] $)
  $}

  ${
    mp3anl1.1 $e |- ph $.
    mp3anl1.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anl1 $p |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an1 imp ) BCHDEABCDEIFABCJDEGKLM $.
      $( [24-Feb-2005] $)
  $}

  ${
    mp3anl2.1 $e |- ps $.
    mp3anl2.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anl2 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an2 imp ) ACHDEABCDEIFABCJDEGKLM $.
      $( [24-Feb-2005] $)
  $}

  ${
    mp3anl3.1 $e |- ch $.
    mp3anl3.2 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anl3 $p |- ( ( ( ph /\ ps ) /\ th ) -> ta ) $=
      ( wa wi w3a ex mp3an3 imp ) ABHDEABCDEIFABCJDEGKLM $.
      $( [24-Feb-2005] $)
  $}

  ${
    mp3anr1.1 $e |- ps $.
    mp3anr1.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anr1 $p |- ( ( ph /\ ( ch /\ th ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl1 ) CDHAEBCDAEFABCDIEGJKJ $.
      $( [4-Nov-2006] $)
  $}

  ${
    mp3anr2.1 $e |- ch $.
    mp3anr2.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anr2 $p |- ( ( ph /\ ( ps /\ th ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl2 ) BDHAEBCDAEFABCDIEGJKJ $.
      $( [24-Nov-2006] $)
  $}

  ${
    mp3anr3.1 $e |- th $.
    mp3anr3.2 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
    $( An inference based on modus ponens. $)
    mp3anr3 $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $=
      ( wa w3a ancoms mp3anl3 ) BCHAEBCDAEFABCDIEGJKJ $.
      $( [19-Oct-2007] $)
  $}

  ${
    mp3an.1 $e |- ph $.
    mp3an.2 $e |- ps $.
    mp3an.3 $e |- ch $.
    mp3an.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mp3an $p |- th $=
      ( mp3an1 mp2an ) BCDFGABCDEHIJ $.
      $( [14-May-1999] $)
  $}

  ${
    mpd3an3.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    mpd3an3.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpd3an3 $p |- ( ( ph /\ ps ) -> th ) $=
      ( wa 3expa mpdan ) ABGCDEABCDFHI $.
      $( [8-Nov-2007] $)
  $}

  ${
    mpd3an23.1 $e |- ( ph -> ps ) $.
    mpd3an23.2 $e |- ( ph -> ch ) $.
    mpd3an23.3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( An inference based on modus ponens. $)
    mpd3an23 $p |- ( ph -> th ) $=
      ( id syl3anc ) AABCDAHEFGI $.
      $( [4-Dec-2006] $)
  $}

  ${
    biimp3a.1 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
    $( Infer implication from a logical equivalence.  Similar to ~ biimpa . $)
    biimp3a $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      ( wa biimpa 3impa ) ABCDABFCDEGH $.
      $( [4-Sep-2005] $)

    $( Infer implication from a logical equivalence.  Similar to ~ biimpar . $)
    biimp3ar $p |- ( ( ph /\ ps /\ th ) -> ch ) $=
      ( exbiri 3imp ) ABDCABCDEFG $.
      $( [2-Jan-2009] $)
  $}

  ${
    3anandis.1 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) /\ ( ph /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent. $)
    3anandis $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $=
      ( w3a wa simpl simpr1 simpr2 simpr3 syl222anc ) ABCDGZHABACADEANIZABCDJOA
      BCDKOABCDLFM $.
      $( [18-Apr-2007] $)
  $}

  ${
    3anandirs.1 $e |- ( ( ( ph /\ th ) /\ ( ps /\ th ) /\ ( ch /\ th ) )
                      -> ta ) $.
    $( Inference that undistributes a triple conjunction in the antecedent. $)
    3anandirs $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $=
      ( w3a wa simpl1 simpr simpl2 simpl3 syl222anc ) ABCGZDHADBDCDEABCDINDJZAB
      CDKOABCDLOFM $.
      $( [18-Apr-2007] $) $( [25-Jul-2006] $)
  $}

  ${
    ecase23d.1 $e |- ( ph -> -. ch ) $.
    ecase23d.2 $e |- ( ph -> -. th ) $.
    ecase23d.3 $e |- ( ph -> ( ps \/ ch \/ th ) ) $.
    $( Deduction for elimination by cases. $)
    ecase23d $p |- ( ph -> ps ) $=
      ( wo wn ioran sylanbrc w3o 3orass sylib ord mt3d ) ABCDHZACIDIQIEFCDJKABQ
      ABCDLBQHGBCDMNOP $.
      $( [15-Jul-2005] $) $( [22-Apr-1994] $)
  $}

  ${
    3ecase.1 $e |- ( -. ph -> th ) $.
    3ecase.2 $e |- ( -. ps -> th ) $.
    3ecase.3 $e |- ( -. ch -> th ) $.
    3ecase.4 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Inference for elimination by cases. $)
    3ecase $p |- th $=
      ( wi 3exp wn a1d pm2.61i pm2.61nii ) BCDABCDIZIABCDHJAKZOBPDCELLMFGN $.
      $( [13-Jul-2005] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
      Other axiomatizations of classical propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz axioms from Meredith's sole axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Carew Meredith's sole axiom for propositional calculus.  This amazing
     formula is thought to be the shortest possible single axiom for
     propositional calculus with inference rule ~ ax-mp , where negation and
     implication are primitive.  Here we prove Meredith's axiom from ~ ax-1 ,
     ~ ax-2 , and ~ ax-3 .  Then from it we derive the Lukasiewicz axioms
     ~ luk-1 , ~ luk-2 , and ~ luk-3 .  Using these we finally re-derive our
     axioms as ~ ax1 , ~ ax2 , and ~ ax3 , thus proving the equivalence of all
     three systems.  C. A. Meredith, "Single Axioms for the Systems (C,N),
     (C,O) and (A,N) of the Two-Valued Propositional Calculus," _The Journal of
     Computing Systems_ vol. 1 (1953), pp. 155-164.  Meredith claimed to be
     close to a proof that this axiom is the shortest possible, but the proof
     was apparently never completed.

     An obscure Irish lecturer, Meredith (1904-1976) became enamored with logic
     somewhat late in life after attending talks by Lukasiewicz and produced
     many remarkable results such as this axiom.  From his obituary:  "He did
     logic whenever time and opportunity presented themselves, and he did it on
     whatever materials came to hand: in a pub, his favored pint of porter
     within reach, he would use the inside of cigarette packs to write proofs
     for logical colleagues."  (The proof was shortened by Andrew Salmon,
     25-Jul-2011.)  (The proof was shortened by Wolf Lammen, 28-May-2013.) $)
  meredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn pm2.21 ax-3 imim12i com13 con1d com12 a1d ax-1 imim1d ja ) ABFZCGDG
    FZFZCFZEEAFZDAFZFUAGZUCUBDUDADAUATAGZDCUERSDCFABHCDIJKLMNEDEAEDOPQ $.
    $( [28-May-2013] $) $( [14-Dec-2002] $)

  $( Theorem ~ meredith restated as an axiom.  This will allow us to ensure
     that the rederivation of ~ ax1 , ~ ax2 , and ~ ax3 below depend only on
     Meredith's sole axiom and not accidentally on a previous theorem above.
     Outside of this section, we will not make use of this axiom. $)
  ax-meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.

  $( Step 3 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (The step numbers refer to Meredith's original paper.) $)
  merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $=
    ( wn wi ax-meredith ax-mp ) DAEZFIBFZEZIFFZJFCJFZFZMDFADFFJDECEFZEKEFZFOFDF
    LFNIBOKDGJPDCLGHDIJAMGH $.
    $( [14-Dec-2002] $)

  $( Step 4 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem2 $p |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) ) $=
    ( wi wn merlem1 ax-meredith ax-mp ) BBDZAECEZDDADAADZDKBDCBDDAJIAFBBACKGH
    $.
    $( [14-Dec-2002] $)

  $( Step 7 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem3 $p |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) ) $=
    ( wi wn merlem2 ax-mp ax-meredith ) AADZCEZJDZDZCDBCDZDZMADCADZDOBEZPDDBDZL
    DZNKKDLDRJKIFKLQFGCABBLHGAACCMHG $.
    $( [14-Dec-2002] $)

  $( Step 8 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem4 $p |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn ax-meredith merlem3 ax-mp ) AADBEZIDDBDZCDCADBADDZDCKDAABBCFKJCGH
    $.
    $( [14-Dec-2002] $)

  $( Step 11 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem5 $p |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) ) $=
    ( wi wn ax-meredith merlem1 merlem4 ax-mp ) BBCZBDZJCCBCBCIICCZABCZADZDZBCC
    ZBBBBBEIJNDCCBCZACZOCZKOCZBBBNAEOKDZCMTCCZACQCZRSCUAUBMBLTFAPUAGHOTAKQEHHH
    $.
    $( [14-Dec-2002] $)

  $( Step 12 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem6 $p |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) ) $=
    ( wi merlem4 merlem3 ax-mp ) BCEZIAEDAEEZECJEADIFJBCGH $.
    $( [14-Dec-2002] $)

  $( Between steps 14 and 15 of Meredith's proof of Lukasiewicz axioms from his
     sole axiom. $)
  merlem7 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) ) $=
    ( wi wn merlem4 merlem6 ax-meredith ax-mp ) BCFZLDFZCEFDGBGFFZDFZFZFZAPFZDN
    LHPAGZFCGZSFFZCFLFZQRFOUAFUBSMOTICEDBUAJKPSCALJKK $.
    $( [22-Dec-2002] $)

  $( Step 15 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem8 $p |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) $=
    ( wph wi wn ax-meredith merlem7 ax-mp ) EEFZEGZLFFEFEFKKFFZABFCFBDFCGAGFFCF
    FEEEEEHMABCDIJ $.
    $( [22-Dec-2002] $)

  $( Step 18 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem9 $p |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ->
                    ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ) $=
    ( wi wn merlem6 merlem8 ax-mp ax-meredith ) CDBEGZGZGZFHZGBHZPGGZBGABGZGZSO
    GFOGGMRHDHGZHAHGZGUAGRGZTNRGUCPCNQIDMRUBJKBEUAARLKOPBFSLK $.
    $( [22-Dec-2002] $)

  $( Step 19 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem10 $p |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) ) $=
    ( wi wn ax-meredith merlem9 ax-mp ) AADZAEZJDDADADIIDDZAABDZDZCLDDZAAAAAFLA
    DJCEDDADZADNDKNDLAACAFOAMCBKGHH $.
    $( [14-Dec-2002] $)

  $( Step 20 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem11 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi wn ax-meredith merlem10 ax-mp ) AACZADZICCACACHHCCZAABCZCZKCZAAAAAELMC
    JMCABLFLKJFGG $.
    $( [14-Dec-2002] $)

  $( Step 28 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem12 $p |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem2 ax-mp merlem4 merlem11 ) CBDDBEZEZAEZMAEZEZNLOBBEKE
    LBBFBKCGHAMLIHMAJH $.
    $( [14-Dec-2002] $)

  $( Step 35 of Meredith's proof of Lukasiewicz axioms from his sole axiom. $)
  merlem13 $p |- ( ( ph -> ps ) ->
              ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) ) $=
    ( wi wn merlem12 merlem5 ax-mp merlem6 ax-meredith merlem11 ) BBEZAFZDCFFCE
    EZNFZEZFZEZEAEZAEZABEQBEETUAEZUASUBOREZREZSRCDGRBEZRFPEZEREUCEZUDSEUFUGQPEU
    FPCDGQPHIRUEUFOJIRBRNUCKIIAMSTJITALIBBAQAKI $.
    $( [14-Dec-2002] $)

  $( 1 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom. $)
  luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi wn ax-meredith merlem13 ax-mp ) CCDZAEZEZEJDDKDBDZBCDACDDZDZABDZMDZCCK
    ABFMADZOEZEZERDDSDLDZNPDOLDTABJIGOLRQGHMASOLFHH $.
    $( [14-Dec-2002] $)

  $( 2 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom. $)
  luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem4 ax-mp merlem11 ax-meredith ) ABZACZJACZCZKAJBZCIBMC
    CZICZICZLOPCZPNQAMDIONEFOIGFAMIJIHFJAGF $.
    $( [14-Dec-2002] $)

  $( 3 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom. $)
  luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi merlem11 merlem1 ax-mp ) ACZHBDZDIDAIDHBEABHIFG $.
    $( [14-Dec-2002] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the standard axioms from the Lukasiewicz axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    luklem1.1 $e |- ( ph -> ps ) $.
    luklem1.2 $e |- ( ps -> ch ) $.
    $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
    luklem1 $p |- ( ph -> ch ) $=
      ( wi luk-1 ax-mp ) BCFZACFZEABFIJFDABCGHH $.
      $( [23-Dec-2002] $)
  $}

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem2 $p |- ( ( ph -> -. ps ) ->
                ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $=
    ( wn wi luk-1 luk-3 ax-mp luklem1 ) ABEZFZBACFZFZMDFBDFFLKCFZMFZNAKCGBOFPNF
    BCHBOMGIJBMDGJ $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem3 $p |- ( ph -> ( ( ( -. ph -> ps ) -> ch ) -> ( th -> ch ) ) ) $=
    ( wn wi luk-3 luklem2 luklem1 ) AAEZDEZFJBFCFDCFFAKGJDBCHI $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem4 $p |- ( ( ( ( -. ph -> ph ) -> ph ) -> ps ) -> ps ) $=
    ( wn wi luk-2 luklem3 ax-mp luk-1 luklem1 ) ACADADZBDZBCZBDZBLJDZKMDJCJDJDZ
    NJEJONDAEJJJLFGGLJBHGBEI $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem5 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wn wi luklem3 luklem4 luklem1 ) AACADADBADZDHAAABEAHFG $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi luk-1 wn luklem5 luklem2 luklem4 luklem1 ax-mp ) AABCZCKBCZKCZKAKBDKEZ
    KCZKCMKCZCZPMOCZQNLCRNBEZNCZLNSFTSBCBCLCLSKBBGBLHIINLKDJMOKDJKPHJI $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem7 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi luk-1 luklem5 luklem1 luklem6 ax-mp ) ABCDZDJCDZACDZDZBLDZAJCEBKDMNDBJ
    KDZKBJBDOBJFJBCEGJCHGBKLEIG $.
    $( [22-Dec-2002] $)

  $( Used to rederive standard propositional axioms from Lukasiewicz'. $)
  luklem8 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi luk-1 luklem7 ax-mp ) CADZABDZCBDZDDIHJDDCABEHIJFG $.
    $( [22-Dec-2002] $)

  $( Standard propositional axiom derived from Lukasiewicz axioms. $)
  ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( luklem5 ) ABC $.
    $( [22-Dec-2002] $)

  $( Standard propositional axiom derived from Lukasiewicz axioms. $)
  ax2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi luklem7 luklem8 luklem6 ax-mp luklem1 ) ABCDDBACDZDZABDZJDZABCEKLAJDZD
    ZMBJAFNJDOMDACGNJLFHII $.
    $( [22-Dec-2002] $)

  $( Standard propositional axiom derived from Lukasiewicz axioms. $)
  ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wn wi luklem2 luklem4 luklem1 ) ACZBCDHADADBADZDIHBAAEAIFG $.
    $( [22-Dec-2002] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'nand' (Sheffer stroke)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c -/\ $. $( 'nand' ) $)
  $( Extend wff definition to include 'nand'. $)
  wnand $a wff ( ph -/\ ps ) $.

  $( Define incompatibility ('not-and' or 'nand').  This is also called the
     Sheffer stroke, represented by a vertical bar, but we use a different
     symbol to avoid ambiguity with other uses of the vertical bar. $)
  df-nand $a |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Derive Nicod's axiom from the standard axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Lemma for handling nested 'nand's. $)
  nic-justlem $p |- ( ( ph -/\ ( ch -/\ ps ) ) <-> ( ph -> ( ch /\ ps ) ) ) $=
    ( wnand wa wn wi df-nand anbi2i xchbinx iman bitr4i ) ACBDZDZACBEZFZEZFAOGN
    AMEQAMHMPACBHIJAOKL $.
    $( [11-Dec-2008] $) $( [19-Nov-2007] $)

  $( Show equivalence between implication and the Nicod version.  To derive
     ~ nic-dfim , apply ~ nic-justbi . $)
  nic-justim $p |- ( ( ph -> ps ) <-> ( ph -/\ ( ps -/\ ps ) ) ) $=
    ( wnand wa wi nic-justlem anidmdbi bitr2i ) ABBCCABBDEABEABBFABGH $.
    $( [17-Dec-2008] $) $( [19-Nov-2007] $)

  $( Show equivalence between negation and the Nicod version.  To derive
     ~ nic-dfneg , apply ~ nic-justbi . $)
  nic-justneg $p |- ( -. ps <-> ( ps -/\ ps ) ) $=
    ( wnand wn wa df-nand anidm xchbinx bicomi ) AABZACIAADAAAEAFGH $.
    $( [16-Dec-2008] $) $( [19-Nov-2007] $)

  $( Show equivalence between the bidirectional and the Nicod version.
     (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  nic-justbi $p |- ( ( ph <-> ps ) <->
          ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) $=
    ( wa wn wo wnand pm4.57 df-nand nic-justneg anbi12i xchbinxr dfbi3 3bitr4ri
    wb xchbinx ) ABCZDZADZBDZCZDZCZDPTEABFZAAFZBBFZFZFZABNPTGUGUCUFCUBUCUFHUCQU
    FUAABHUFUDUECTUDUEHRUDSUEAIBIJKJOABLM $.
    $( [11-Dec-2008] $) $( [19-Nov-2007] $)

$( [suppress from the Table of Contents by breaking whitespace before "=-=-"]
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Prove Nicod's axiom and implication and negation definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define implication in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ( ps -/\ ps ) ) <-> ( ph -> ps ) ) ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     a definition ($a statement). $)
  nic-dfim $p |- ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -> ps ) ) -/\
                   ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -/\ ( ps -/\ ps ) ) )
                          -/\
                     ( ( ph -> ps ) -/\ ( ph -> ps ) ) ) ) $=
    ( wnand wi wb nic-justim bicomi nic-justbi mpbi ) ABBCCZABDZEJKCJJCKKCCCKJA
    BFGJKHI $.
    $( [11-Dec-2008] $)

  $( Define negation in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ph ) <-> -. ph ) ` .  In a pure (standalone) treatment of
     Nicod's axiom, this theorem would be changed to a definition ($a
     statement). $)
  nic-dfneg $p |- ( ( ( ph -/\ ph ) -/\ -. ph ) -/\
                    ( ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) -/\
                      ( -. ph -/\ -. ph ) ) ) $=
    ( wnand wn wb nic-justneg bicomi nic-justbi mpbi ) AABZACZDIJBIIBJJBBBJIAEF
    IJGH $.
    $( [11-Dec-2008] $)

  ${
    $( Minor premise. $)
    nic-jmin $e |- ph $.
    $( Major premise. $)
    nic-jmaj $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Derive Nicod's rule of modus ponens using 'nand', from the standard
       one.  Although the major and minor premise together also imply ` ch ` ,
       this form is necessary for useful derivations from ~ nic-ax .  In a pure
       (standalone) treatment of Nicod's axiom, this theorem would be changed
       to an axiom ($a statement).  (Contributed by Jeff Hoffman,
       19-Nov-2007.) $)
    nic-mp $p |- ps $=
      ( wnand wa wi nic-justlem mpbi simprd ax-mp ) ABDACBACBFFACBGHEABCIJKL $.
      $( [11-Dec-2008] $) $( [19-Nov-2007] $)

    $( A direct proof of ~ nic-mp . $)
    nic-mpALT $p |- ps $=
      ( wa wi wn wnand df-nand anbi2i xchbinx mpbi iman mpbir simprd ax-mp ) AB
      DACBACBFZGARHZFZHZACBIZIZUAEUCAUBFTAUBJUBSACBJKLMARNOPQ $.
      $( [30-Dec-2008] $)
  $}

  $( Nicod's axiom derived from the standard ones.  See _Intro. to Math.
     Phil._ by B. Russell, p. 152.  Like ~ meredith , the usual axioms can be
     derived from this and vice versa.  Unlike ~ meredith , Nicod uses a
     different connective ('nand'), so another form of modus ponens must be
     used in proofs, e.g. { ~ nic-ax , ~ nic-mp  } is equivalent to
     { ~ luk-1 , ~ luk-2 , ~ luk-3 , ~ ax-mp }.  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     an axiom ($a statement).  (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  nic-ax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\
                   ( ( ta -/\ ( ta -/\ ta ) ) -/\
                     ( ( th -/\ ch ) -/\
                       ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnand wa wi nic-justlem biimpi simpl imim2i wn df-nand bitr4i con3 imim2d
    imnan con2b mpbir 3bitr4ri syl6ibr syl5bir nic-justim sylib pm4.24 jctil
    3syl ) ACBFFZEEEFFZDCFZADFZULFFZFFUIUJUMGHUIUMUJUIACBGZHZACHZUMUIUOABCIJUNC
    ACBKLUPUKULHUMUKDCMZHZUPULURDCGMUKDCRDCNOUPURDAMZHZULUPUQUSDACPQADMHADGMUTU
    LADRDASADNUAUBUCUKULUDUEUHUJEEEGZHEVAEUFJEEEITUGUIUMUJIT $.
    $( [11-Dec-2008] $) $( [19-Nov-2007] $)

  $( A direct proof of ~ nic-ax . $)
  nic-axALT $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnand wa wn anidm df-nand anbi2i notbii iman 3bitr4i imnan bitr4i xchbinx
    wi anbi12i mpbir simpl imim2i con3 imim2d biimpri jctil con2b bitr3i 3bitri
    syl ) ACBFZFZEEEFZFZDCFZADFZUPFZFZFZFULUSGZHZVAACBGZRZEEEGZRZDCHZRZDAHZRZRZ
    GZRZVCVJVEVCACRZVJVBCACBUAUBVMVFVHDACUCUDUJVDEEIUEUFVAVCVKHZGZHVLUTVOULVCUS
    VNAUKGZHAVBHZGZHULVCVPVRUKVQACBJKLAUKJAVBMNUSUNURGVKUNURJUNVEURVJEUMGZHEVDH
    ZGZHUNVEVSWAUMVTEEEJKLEUMJEVDMNUOUQGZHVGVIHZGZHURVJWBWDUOVGUQWCUODCGHVGDCJD
    COPUQUPUPGZVIUPUPJWEUPADGHZVIUPIADJWFADHRVIADOADUGUHUIQSLUOUQJVGVIMNSQSLVCV
    KMPTULUSJT $.
    $( [11-Dec-2008] $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Derive the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-imp.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference for ~ nic-mp using ~ nic-ax as major premise.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.) $)
    nic-imp $p |- ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
      ( wta wnand nic-ax nic-mp ) ACBGGDCGADGZJGGFFFGGEABCDFHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  $( Lemma for ~ nic-id . $)
  nic-idlem1 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\
                 ( ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) -/\
                   ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) ) $=
    ( wnand nic-ax nic-imp ) ACBFFACFAAFZIFFEEEFFDABCAEGH $.
    $( [11-Dec-2008] $) $( [17-Nov-2007] $)

  ${
    nic-idlem2.1 $e |- ( et -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) $.
    $( Lemma for ~ nic-id .  Inference used by ~ nic-id . $)
    nic-idlem2 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ et ) $=
      ( wnand nic-ax nic-imp nic-mp ) FACBHHZDHZHDEEEHHZHZFHZPGOMMFLACHAAHZQHHN
      DABCAEIJJK $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  $( Theorem ~ id expressed with ` -/\ ` .  (Contributed by Jeff Hoffman,
     17-Nov-2007.) $)
  nic-id $p |- ( ta -/\ ( ta -/\ ta ) ) $=
    ( wph wps wch wth wnand nic-ax nic-idlem2 nic-idlem1 nic-mp ) BCFZCBFZLFFZD
    DDFZFZFZCCCFFZFAAAFFZOEEEMDQCCCBEGHMNDPCORFKLLOAIHJ $.
    $( [11-Dec-2008] $) $( [17-Nov-2007] $)

  $( ` -/\ ` is symmetric.  (Contributed by Jeff Hoffman, 17-Nov-2007.) $)
  nic-swap $p |- ( ( th -/\ ph ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
    ( wta wnand nic-id nic-ax nic-mp ) AAADDBADABDZHDDCCCDDAEAAABCFG $.
    $( [11-Dec-2008] $) $( [17-Nov-2007] $)

  ${
    nic-isw1.1 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-swap .  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-isw1 $p |- ( ph -/\ th ) $=
      ( wnand nic-swap nic-mp ) BADABDZGCABEF $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-isw2.1 $e |- ( ps -/\ ( th -/\ ph ) ) $.
    $( Inference for swapping nested terms.  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-isw2 $p |- ( ps -/\ ( ph -/\ th ) ) $=
      ( wnand nic-swap nic-imp nic-mp nic-isw1 ) BACEZBCAEZEJBEZLDJKKBCAFGHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-iimp1.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    nic-iimp1.2 $e |- ( th -/\ ch ) $.
    $( Inference version of ~ nic-imp using right-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.) $)
    nic-iimp1 $p |- ( th -/\ ph ) $=
      ( wnand nic-imp nic-mp nic-isw1 ) DADCGADGZKFABCDEHIJ $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-iimp2.1 $e |- ( ( ph -/\ ps ) -/\ ( ch -/\ ch ) ) $.
    nic-iimp2.2 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-imp using left-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.) $)
    nic-iimp2 $p |- ( th -/\ ( ch -/\ ch ) ) $=
      ( wnand nic-isw1 nic-iimp1 ) CCGZBADJABGEHFI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-idel.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference to remove the trailing term.  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-idel $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnand nic-id nic-isw1 nic-imp nic-mp ) CCEZCEAJEZKJCCFGABCJDHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-ich.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    nic-ich.2 $e |- ( ps -/\ ( ch -/\ ch ) ) $.
    $( Chained inference.  (Contributed by Jeff Hoffman, 17-Nov-2007.) $)
    nic-ich $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnand nic-isw1 nic-imp nic-mp ) CCFZBFAJFZKJBEGABBJDHI $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

  ${
    nic-idbl.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    $( Double the terms.  Since doubling is the same as negation, this can be
       viewed as a contraposition inference.  (Contributed by Jeff Hoffman,
       17-Nov-2007.) $)
    nic-idbl $p |- ( ( ps -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) ) $=
      ( wnand nic-imp nic-ich ) BBDABDAADABBBCEABBACEF $.
      $( [11-Dec-2008] $) $( [17-Nov-2007] $)
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Biconditional justification from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( For nic-* definitions, the biconditional connective is not used.  Instead,
     definitions are made based on this form. ~ nic-bi1 and ~ nic-bi2 are used
     to convert the definitions into usable theorems about one side of the
     implication.  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
  nic-bijust $p |- ( ( ta -/\ ta ) -/\ ( ( ta -/\ ta ) -/\ ( ta -/\ ta ) ) ) $=
    ( nic-swap ) AAB $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

  ${
    $( 'Biconditional' premise.  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
    nic-bi1.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract one side of an implication from a definition. $)
    nic-bi1 $p |- ( ph -/\ ( ps -/\ ps ) ) $=
      ( wnand nic-id nic-iimp1 nic-isw2 nic-idel ) AABBAAABDBBDAADACAEFGH $.
      $( [11-Dec-2008] $) $( [18-Nov-2007] $)
  $}

  ${
    $( 'Biconditional' premise.  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
    nic-bi2.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract the other side of an implication from a
       'biconditional' definition. $)
    nic-bi2 $p |- ( ps -/\ ( ph -/\ ph ) ) $=
      ( wnand nic-isw2 nic-id nic-iimp1 nic-idel ) BBAABDZAADZBBDZBKIJCEBFGH $.
      $( [11-Dec-2008] $) $( [18-Nov-2007] $)
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Prove the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-smin $e |- ph $.
    $( Major premise. $)
    nic-smaj $e |- ( ph -> ps ) $.
    $( Derive the standard modus ponens from ~ nic-mp .  (Contributed by Jeff
       Hoffman, 18-Nov-2007.) $)
    nic-stdmp $p |- ps $=
      ( wi wnand nic-dfim nic-bi2 nic-mp ) ABBCABEZABBFFZKDKJABGHII $.
      $( [11-Dec-2008] $) $( [18-Nov-2007] $)
  $}

  $( Proof of ~ luk-1 from ~ nic-ax and ~ nic-mp (and definitions ~ nic-dfim
     and ~ nic-dfneg ).  Note that the standard axioms ~ ax-1 , ~ ax-2 , and
     ~ ax-3 are proved from the Lukasiewicz axioms by theorems ~ ax1 , ~ ax2 ,
     and ~ ax3 .  (Contributed by Jeff Hoffman, 18-Nov-2007.) $)
  nic-luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wta wi nic-dfim nic-bi2 nic-ax nic-isw2 nic-idel nic-bi1 nic-idbl nic-imp
    wnand nic-swap nic-ich nic-mp ) ABEZBCEZACEZEZUANNZRUAEZUCRABBNNZUAUDRABFGU
    DSTTNZNZUAUDCCNZBNZAUGNZUINZNZUFUDDDDNNZUKUKUDULABBUGDHIJUKUEUHNUFUEUJUJUHU
    ITUITACFKLMSUHUHUESBUGNZUHUMSBCFGUGBOPMPPUFUASTFKPPUBUCRUAFKQ $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

  $( Proof of ~ luk-2 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.) $)
  nic-luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi wnand nic-dfim nic-bi2 nic-dfneg nic-id nic-iimp1 nic-isw2 nic-isw1
    nic-bi1 nic-mp ) ABZACZAADZDZOACZROPONPDZSPSONAEFNPPPNDNNDPPDPAGPHIJIKQROAE
    LM $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

  $( Proof of ~ luk-3 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.) $)
  nic-luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi wnand nic-dfim nic-bi1 nic-dfneg nic-bi2 nic-id nic-iimp1 nic-iimp2
    nic-mp ) AACZBDZOEEZAODZQNBBEZOANREONBFGNAAEZSASNAHIAJKLPQAOFGM $.
    $( [11-Dec-2008] $) $( [18-Nov-2007] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                True and false constants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c T. $.
  $c F. $.

  $( ` T. ` is a wff. $)
  wtru $a wff T. $.

  $( ` F. ` is a wff. $)
  wfal $a wff F. $.

  $( Soundness justification theorem for ~ df-tru . $)
  trujust $p |- ( ( ph <-> ph ) <-> ( ps <-> ps ) ) $=
    ( wb biid 2th ) AACBBCADBDE $.
    $( [17-Nov-2013] $)

  $( Definition of ` T. ` , a tautology. ` T. ` is a constant true.  In this
     definition ~ biid is used as an antecedent, however, any true wff, such as
     an axiom, can be used in its place. $)
  df-tru $a |- ( T. <-> ( ph <-> ph ) ) $.

  $( Definition of ` F. ` , a contradiction. ` F. ` is a constant false. $)
  df-fal $a |- ( F. <-> -. T. ) $.

  $( ` T. ` is provable.  (Contributed by Anthony Hart, 13-Oct-2010.) $)
  tru $p |- T. $=
    ( wph wtru wb biid df-tru mpbir ) BAACADAEF $.
    $( [6-Sep-2010] $) $( [13-Oct-2010] $)

  $( ` F. ` is not provable.  (Contributed by Anthony Hart, 22-Oct-2010.)  (The
     proof was shortened by Mel L. O'Cat, 11-Mar-2012.) $)
  notfal $p |- -. F. $=
    ( wfal wtru wn tru notnoti df-fal mtbir ) ABCBDEFG $.
    $( [11-Mar-2012] $) $( [22-Oct-2010] $)

  ${
    trud.1 $e |- ( T. -> ph ) $.
    $( Eliminate ` T. ` as an antecedent.  (Contributed by Mario Carneiro,
       13-Mar-2014.) $)
    trud $p |- ph $=
      ( wtru tru ax-mp ) CADBE $.
      $( [13-Mar-2014] $)
  $}

  $( One definition of negation in logics that take ` F. ` as axiomatic is via
     "implies contradition", i.e. ` ph -> F. ` .
     (Contributed by Mario Carneiro, 2-Feb-2015.) $)
  dfneg $p |- ( -. ph <-> ( ph -> F. ) ) $=
    ( wfal wn wi wb notfal mtt ax-mp ) BCACABDEFBAGH $.
    $( [2-Feb-2015] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Auxiliary theorems for Alan Sare's virtual deduction tool, part 1
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ee22.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee22.2 $e |- ( ph -> ( ps -> th ) ) $.
    ee22.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Special theorem needed for Alan Sare's virtual deduction translation
       tool.  (Contributed by Alan Sare, 2-May-2011.) $)
    ee22 $p |- ( ph -> ( ps -> ta ) ) $=
      ( syl6c ) ABCDEFGHI $.
      $( [28-Oct-2011] $) $( [2-May-2011] $)
  $}

  ${
    ee12an.1 $e |- ( ph -> ps ) $.
    ee12an.2 $e |- ( ph -> ( ch -> th ) ) $.
    ee12an.3 $e |- ( ( ps /\ th ) -> ta ) $.
    $( Special theorem needed
       for Alan Sare's virtual deduction translation tool.  (Contributed by
       Alan Sare, 28-Oct-2011.) $)
    ee12an $p |- ( ph -> ( ch -> ta ) ) $=
      ( wa jctild syl6 ) ACBDIEACDBGFJHK $.
      $( [28-Oct-2011] $) $( [28-Oct-2011] $)
  $}

  ${
    ee23.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee23.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    ee23.3 $e |- ( ch -> ( ta -> et ) ) $.
    $( Special theorem needed
       for Alan Sare's virtual deduction translation tool.
       (Contributed by Alan Sare,
       17-Jul-2011.) $)
    ee23 $p |- ( ph -> ( ps -> ( th -> et ) ) ) $=
      ( wi syl6 syldd ) ABDEFHABCEFJGIKL $.
      $( [17-Jul-2011] $)
  $}

  $( Exportation implication also converting head from biconditional to
     conditional.  (Contributed by Alan Sare, 31-Dec-2011.) $)
  exbir $p |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) ->
              ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wa wb wi bi2 imim2i exp3a ) ABEZCDFZGABDCGZLMKCDHIJ $.
    $( [31-Dec-2011] $)

  $( ~ impexp with a 3-conjunct antecedent.  (Contributed by Alan Sare,
     31-Dec-2011.) $)
  3impexp $p |- ( ( ( ph /\ ps /\ ch ) -> th ) <->
                ( ph -> ( ps -> ( ch -> th ) ) ) ) $=
    ( w3a wi id 3expd 3impd impbii ) ABCEDFZABCDFFFZKABCDKGHLABCDLGIJ $.
    $( [31-Dec-2011] $)

  $( ~ 3impexp with biconditional consequent of antecedent that is commuted in
     consequent.  (Contributed by
     Alan Sare, 31-Dec-2011.) $)
  3impexpbicom $p |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <->
                     ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) ) $=
    ( w3a wb wi bicom imbi2 biimpcd mpi 3expd 3impexp biimpri syl6ibr impbii )
    ABCFZDEGZHZABCEDGZHHHZTABCUATSUAGZRUAHZDEIZUCTUDSUARJKLMUBRUASUDUBABCUANOUE
    PQ $.
    $( [31-Dec-2011] $)

  ${
    3impexpbicomi.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $.
    $( Deduction form of ~ 3impexpbicom .
       (Contributed by Alan Sare, 31-Dec-2011.) $)
    3impexpbicomi $p |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) $=
      ( wb w3a bicomd 3exp ) ABCEDGABCHDEFIJ $.
      $( [31-Dec-2011] $)
  $}

  $( Closed form of ~ ancoms .
     (Contributed by Alan Sare, 31-Dec-2011.) $)
  ancomsimp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) ) $=
    ( wa ancom imbi1i ) ABDBADCABEF $.
    $( [31-Dec-2011] $)

  ${
    exp3acom3r.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Export and commute antecedents.  (Contributed by Alan Sare,
       18-Mar-2012.) $)
    exp3acom3r $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      ( exp3a com3l ) ABCDABCDEFG $.
      $( [18-Mar-2012] $)
  $}

  $( Implication form of ~ exp3acom23 .(Contributed by Alan Sare,
     22-Jul-2012.) $)
  exp3acom23g $p |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <->
                        ( ph -> ( ch -> ( ps -> th ) ) ) ) $=
    ( wa wi ancomsimp impexp bitri imbi2i ) BCEDFZCBDFFZAKCBEDFLBCDGCBDHIJ $.
    $( [22-Jul-2012] $)

  ${
    exp3acom23.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( The exportation deduction ~ exp3a with commutation of the conjoined
       wwfs.  (Contributed by Alan Sare, 22-Jul-2012.) $)
    exp3acom23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      ( exp3a com23 ) ABCDABCDEFG $.
      $( [22-Jul-2012] $)
  $}

  $( Implication form of ~ simplbi2com .  (Contributed by Alan Sare,
     22-Jul-2012.) $)
  simplbi2comg $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) ) $=
    ( wa wb bi2 exp3acom23 ) ABCDZEBCAAHFG $.
    $( [22-Jul-2012] $)

  ${
    simplbi2com.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( A deduction eliminating a conjunct, similar to ~ simplbi2 .
       (Contributed by Alan Sare, 22-Jul-2012.)  (The proof was shortened by
       Wolf Lammen, 10-Nov-2012.) $)
    simplbi2com $p |- ( ch -> ( ps -> ph ) ) $=
      ( simplbi2 com12 ) BCAABCDEF $.
      $( [10-Nov-2012] $) $( [22-Jul-2012] $)
  $}

  ${
    ee21.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee21.2 $e |- ( ph -> th ) $.
    ee21.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Special theorem needed
       for Alan Sare's virtual deduction translation tool.
       (Contributed by Alan Sare, 18-Mar-2012.)  $)
    ee21 $p |- ( ph -> ( ps -> ta ) ) $=
      ( a1d ee22 ) ABCDEFADBGIHJ $.
      $( [18-Mar-2012] $)
  $}

  ${
    ee10.1 $e |- ( ph -> ps ) $.
    ee10.2 $e |- ch $.
    ee10.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( Special theorem needed
       for Alan Sare's virtual deduction translation tool. $)
    ee10 $p |- ( ph -> th ) $=
      ( mpi syl ) ABDEBCDFGHI $.
      $( [25-Jul-2011] $)
  $}

  ${
    ee02.1 $e |- ph $.
    ee02.2 $e |- ( ps -> ( ch -> th ) ) $.
    ee02.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( Special theorem needed
       for Alan Sare's virtual deduction translation tool. $)
    ee02 $p |- ( ps -> ( ch -> ta ) ) $=
      ( a1i sylsyld ) BACDEABFIGHJ $.
      $( [22-Jul-2012] $)
  $}

$( End of auxiliary theorems for Alan Sare's virtual deduction tool, part 1 $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
        Predicate calculus mostly without distinct variables
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  "Pure" (equality-free) predicate calculus axioms ax-5, ax-6, ax-7, ax-gen
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new symbols needed for pure predicate calculus. $)
  $c A. $. $( "inverted A" universal quantifier (read:  "for all") $)
  $c set $. $( Individual variable type (read:  "the following is an
             individual (set) variable" $)

  $( Declare some names for individual variables. $)
  $v x $.
  $v y $.
  $v z $.
  $v w $.
  $v v $.
  $v u $.
  $( Let ` x ` be an individual variable. $)
  vx $f set x $.
  $( Let ` y ` be an individual variable. $)
  vy $f set y $.
  $( Let ` z ` be an individual variable. $)
  vz $f set z $.
  $( Let ` w ` be an individual variable. $)
  vw $f set w $.
  $( Let ` v ` be an individual variable. $)
  vv $f set v $.
  $( Let ` u ` be an individual variable. $)
  vu $f set u $.

  $( Extend wff definition to include the universal quantifier ('for all').
     ` A. x ph ` is read " ` ph ` (phi) is true for all ` x ` ."  Typically, in
     its final application ` ph ` would be replaced with a wff containing a
     (free) occurrence of the variable ` x ` , for example ` x = y ` .  In a
     universe with a finite number of objects, "for all" is equivalent to a big
     conjunction (AND) with one wff for each possible case of ` x ` .  When the
     universe is infinite (as with set theory), such a propositional-calculus
     equivalent is not possible because an infinitely long formula has no
     meaning, but conceptually the idea is the same. $)
  wal $a wff A. x ph $.

  $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105. $)
  ax-5 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113. $)
  ax-6 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.

  $( Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  One of the 4 axioms of pure predicate calculus.  Axiom
     scheme C6' in [Megill] p. 448 (p. 16 of the preprint).  Also appears as
     Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of [Monk2] p. 113.  An alternate
     axiomatization could use ~ ax467 in place of ~ ax-4 , ~ ax-6o , and
     ~ ax-7 . $)
  ax-7 $a |- ( A. x A. y ph -> A. y A. x ph ) $.

  ${
    ax-g.1 $e |- ph $.
    $( Rule of Generalization.  The postulated inference rule of pure predicate
       calculus.  See e.g.  Rule 2 of [Hamilton] p. 74.  This rule says that if
       something is unconditionally true, then it is true for all values of a
       variable.  For example, if we have proved ` x = x ` , we can conclude
       ` A. x x = x ` or even ` A. y x = x ` .  Theorem ~ a4i shows we can go
       the other way also: in other words we can add or remove universal
       quantifiers from the beginning of any theorem as required. $)
    ax-gen $a |- A. x ph $.
  $}

  ${
    gen2.1 $e |- ph $.
    $( Generalization applied twice. $)
    gen2 $p |- A. x A. y ph $=
      ( wal ax-gen ) ACEBACDFF $.
      $( [30-Apr-1998] $)
  $}

  ${
    mpg.1 $e |- ( A. x ph -> ps ) $.
    mpg.2 $e |- ph $.
    $( Modus ponens combined with generalization. $)
    mpg $p |- ps $=
      ( wal ax-gen ax-mp ) ACFBACEGDH $.
      $( [24-May-1994] $)
  $}

  ${
    mpgbi.1 $e |- ( A. x ph <-> ps ) $.
    mpgbi.2 $e |- ph $.
    $( Modus ponens on biconditional combined with generalization.  (The proof
       was shortened by Stefan Allan, 28-Oct-2008.) $)
    mpgbi $p |- ps $=
      ( wal ax-gen mpbi ) ACFBACEGDH $.
      $( [31-Oct-2008] $) $( [24-May-1994] $)
  $}

  ${
    mpgbir.1 $e |- ( ph <-> A. x ps ) $.
    mpgbir.2 $e |- ps $.
    $( Modus ponens on biconditional combined with generalization.  (The proof
       was shortened by Stefan Allan, 28-Oct-2008.) $)
    mpgbir $p |- ph $=
      ( wal ax-gen mpbir ) ABCFBCEGDH $.
      $( [31-Oct-2008] $) $( [24-May-1994] $)
  $}

  ${
    a7s.1 $e |- ( A. x A. y ph -> ps ) $.
    $( Swap quantifiers in an antecedent. $)
    a7s $p |- ( A. y A. x ph -> ps ) $=
      ( wal ax-7 syl ) ACFDFADFCFBADCGEH $.
      $( [5-Aug-1993] $)
  $}

  ${
    alimi.1 $e |- ( ph -> ps ) $.
    $( Inference quantifying both antecedent and consequent. $)
    alimi $p |- ( A. x ph -> A. x ps ) $=
      ( wi wal ax-5 mpg ) ABEACFBCFECABCGDH $.
      $( [5-Aug-1993] $)

    $( Inference doubly quantifying both antecedent and consequent. $)
    2alimi $p |- ( A. x A. y ph -> A. x A. y ps ) $=
      ( wal alimi ) ADFBDFCABDEGG $.
      $( [3-Feb-2005] $)
  $}

  $( Theorem 19.20 of [Margaris] p. 90.  (The proof was shortened by O'Cat,
     30-Mar-2008.) $)
  alim $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( ax-5 ) ABCD $.
    $( [30-Mar-2008] $) $( [5-Aug-1993] $)

  ${
    al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference quantifying antecedent, nested antecedent, and consequent. $)
    al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $=
      ( wal wi alimi alim syl ) ADFBCGZDFBDFCDFGAKDEHBCDIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Variant of ~ al2imi with conjunctive antecedent.  (Contributed by Andrew
       Salmon, 8-Jun-2011.) $)
    alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $=
      ( wal ex al2imi imp ) ADFBDFCDFABCDABCEGHI $.
      $( [8-Jun-2011] $)
  $}

  ${
    alimd.1 $e |- ( ph -> A. x ph ) $.
    alimd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90. $)
    alimd $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( wal wi al2imi syl ) AADGBDGCDGHEABCDFIJ $.
      $( [4-Jan-2002] $)
  $}

  $( Theorem 19.15 of [Margaris] p. 90. $)
  albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $=
    ( wb wal bi1 al2imi bi2 impbid ) ABDZCEACEBCEJABCABFGJBACABHGI $.
    $( [5-Aug-1993] $)

  ${
    alrimi.1 $e |- ( ph -> A. x ph ) $.
    alrimi.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90. $)
    alrimi $p |- ( ph -> A. x ps ) $=
      ( wal alimi syl ) AACFBCFDABCEGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    albii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding universal quantifier to both sides of an
       equivalence. $)
    albii $p |- ( A. x ph <-> A. x ps ) $=
      ( wb wal albi mpg ) ABEACFBCFECABCGDH $.
      $( [7-Aug-1994] $)

    $( Inference adding 2 universal quantifiers to both sides of an
       equivalence. $)
    2albii $p |- ( A. x A. y ph <-> A. x A. y ps ) $=
      ( wal albii ) ADFBDFCABDEGG $.
      $( [9-Mar-1997] $)
  $}

  ${
    hbth.1 $e |- ph $.
    $( No variable is (effectively) free in a theorem.

       This and later "hypothesis-building" lemmas, with labels starting
       "hb...", allow us to construct proofs of formulas of the form
       ` |- ( ph -> A. x ph ) ` from smaller formulas of this form.  These are
       useful for constructing hypotheses that state " ` x ` is (effectively)
       not free in ` ph ` ." $)
    hbth $p |- ( ph -> A. x ph ) $=
      ( wal ax-gen a1i ) ABDAABCEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    hbxfrbi.1 $e |- ( ph <-> ps ) $.
    hbxfrbi.2 $e |- ( ps -> A. x ps ) $.
    $( A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  (Contributed by
       Jonathan Ben-Naim, 3-Jun-2011.) $)
    hbxfrbi $p |- ( ph -> A. x ph ) $=
      ( wal albii 3imtr4i ) BBCFAACFEDABCDGH $.
      $( [3-Jun-2011] $)
  $}

  ${
    hbal.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` . $)
    hbal $p |- ( A. y ph -> A. x A. y ph ) $=
      ( wal alimi ax-7 syl ) ACEZABEZCEIBEAJCDFACBGH $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem 19.5 of [Margaris] p. 89. $)
  alcom $p |- ( A. x A. y ph <-> A. y A. x ph ) $=
    ( wal ax-7 impbii ) ACDBDABDCDABCEACBEF $.
    $( [5-Aug-1993] $)

  ${
    alrimd.1 $e |- ( ph -> A. x ph ) $.
    alrimd.2 $e |- ( ps -> A. x ps ) $.
    alrimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (The proof was
       shortened by Andrew Salmon, 13-May-2011.) $)
    alrimd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wal alimd syl5 ) BBDHACDHFABCDEGIJ $.
      $( [16-May-2011] $) $( [10-Feb-1997] $)
  $}

  ${
    albid.1 $e |- ( ph -> A. x ph ) $.
    albid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule). $)
    albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( wb wal alrimi albi syl ) ABCGZDHBDHCDHGALDEFIBCDJK $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem 19.26 of [Margaris] p. 90.  Also Theorem *10.22 of
     [WhiteheadRussell] p. 119.  (The proof was shortened by Wolf Lammen,
     4-Jul-2014.) $)
  19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
    ( wa wal simpl alimi simpr jca id alanimi impbii ) ABDZCEZACEZBCEZDNOPMACAB
    FGMBCABHGIABMCMJKL $.
    $( [4-Jul-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ 19.26 as of 4-Jul-2014. $)
  19.26OLD $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
    ( wa wal simpl alimi simpr jca pm3.2 al2imi imp impbii ) ABDZCEZACEZBCEZDOP
    QNACABFGNBCABHGIPQOABNCABJKLM $.
    $( [5-Aug-1993] $)

  $( Theorem 19.26 of [Margaris] p. 90 with two quantifiers. $)
  19.26-2 $p |- ( A. x A. y ( ph /\ ps ) <->
                ( A. x A. y ph /\ A. x A. y ps ) ) $=
    ( wa wal 19.26 albii bitri ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.
    $( [3-Feb-2005] $)

  $( Theorem 19.26 of [Margaris] p. 90 with triple conjunction. $)
  19.26-3an $p |- ( A. x ( ph /\ ps /\ ch )
                   <-> ( A. x ph /\ A. x ps /\ A. x ch ) ) $=
    ( wa wal w3a 19.26 anbi1i bitri df-3an albii 3bitr4i ) ABEZCEZDFZADFZBDFZEZ
    CDFZEZABCGZDFQRTGPNDFZTEUANCDHUCSTABDHIJUBODABCKLQRTKM $.
    $( [13-Sep-2011] $)

  $( Theorem 19.33 of [Margaris] p. 90. $)
  19.33 $p |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $=
    ( wal wo orc alimi olc jaoi ) ACDABEZCDBCDAJCABFGBJCBAHGI $.
    $( [5-Aug-1993] $)

  $( Theorem *11.21 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  alrot3 $p |- ( A. x A. y A. z ph <-> A. y A. z A. x ph ) $=
    ( wal alcom albii bitri ) ADEZCEBEIBEZCEABEDEZCEIBCFJKCABDFGH $.
    $( [24-May-2011] $)

  $( Rotate 4 universal quantifiers twice.  (The proof was shortened by Wolf
     Lammen, 28-Jun-2014.) $)
  alrot4 $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $=
    ( wal alrot3 albii alcom 3bitri ) AEFDFCFZBFACFZEFZDFZBFMBFZDFLBFEFZDFKNBAC
    DEGHMBDIOPDLBEIHJ $.
    $( [28-Jun-2014] $) $( [2-Feb-2005] $)

  $( Obsolete proof of ~ alrot4 as of 28-Jun-2014. $)
  alrot4OLD $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $=
    ( wal alcom albii bitri 3bitri ) AEFZDFCFZBFACFZEFZDFZBFNBFZDFMBFEFZDFLOBLK
    CFZDFOKCDGRNDACEGHIHNBDGPQDMBEGHJ $.
    $( [2-Feb-2005] $)

  $( Split a biconditional and distribute quantifier. $)
  albiim $p |- ( A. x ( ph <-> ps ) <->
             ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $=
    ( wb wal wi wa dfbi2 albii 19.26 bitri ) ABDZCEABFZBAFZGZCEMCENCEGLOCABHIMN
    CJK $.
    $( [18-Aug-1993] $)

  $( Split a biconditional and distribute 2 quantifiers. $)
  2albiim $p |- ( A. x A. y ( ph <-> ps ) <->
             ( A. x A. y ( ph -> ps ) /\ A. x A. y ( ps -> ph ) ) ) $=
    ( wb wal wi wa albiim albii 19.26 bitri ) ABEDFZCFABGDFZBAGDFZHZCFNCFOCFHMP
    CABDIJNOCKL $.
    $( [3-Feb-2005] $)

  ${
    hband.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hband.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hban . $)
    hband $p |- ( ph -> ( ( ps /\ ch ) -> A. x ( ps /\ ch ) ) ) $=
      ( wa wal anim12d 19.26 syl6ibr ) ABCGZBDHZCDHZGLDHABMCNEFIBCDJK $.
      $( [2-Jan-2002] $)
  $}

  ${
    hb3and.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hb3and.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    hb3and.3 $e |- ( ph -> ( th -> A. x th ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hb3an . $)
    hb3and $p |- ( ph -> ( ( ps /\ ch /\ th ) -> A. x ( ps /\ ch /\ th ) ) ) $=
      ( w3a wal 3anim123d 19.26-3an syl6ibr ) ABCDIZBEJZCEJZDEJZINEJABOCPDQFGHK
      BCDELM $.
      $( [17-Feb-2013] $)
  $}

  ${
    hbald.1 $e |- ( ph -> A. y ph ) $.
    hbald.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbal . $)
    hbald $p |- ( ph -> ( A. y ps -> A. x A. y ps ) ) $=
      ( wal alimd ax-7 syl6 ) ABDGZBCGZDGKCGABLDEFHBDCIJ $.
      $( [2-Jan-2002] $)
  $}

  $( Declare the existential quantifier symbol. $)
  $c E. $.   $( Backwards E (read:  "there exists") $)

  $( Extend wff definition to include the existential quantifier ("there
     exists"). $)
  wex $a wff E. x ph $.

  $( ` x ` is bound in ` E. x ph ` .  Axiom 9 of 10 for intuitionistic logic. $)
  ax-ie1 $a |- ( E. x ph -> A. x E. x ph ) $.

  $( Define existential quantification. ` E. x ph ` means "there exists at
     least one set ` x ` such that ` ph ` is true."
     Axiom 10 of 10 for intuitionistic logic. $)
  ax-ie2 $a |- ( A. x ( ps -> A. x ps ) ->
               ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $.

  $( ` x ` is not free in ` E. x ph ` . $)
  hbe1 $p |- ( E. x ph -> A. x E. x ph ) $=
    ( ax-ie1 ) ABC $.
    $( [5-Aug-1993] $)

  $( Closed form of Theorem 19.23 of [Margaris] p. 90.
     (Revised by Mario Carneiro, 1-Feb-2015.) $)
  19.23t $p |- ( A. x ( ps -> A. x ps ) ->
               ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( ax-ie2 ) ABCD $.
    $( [1-Feb-2015] $) $( [7-Nov-2005] $)

  ${
    19.23.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.23 of [Margaris] p. 90.
       (Revised by Mario Carneiro, 1-Feb-2015.) $)
    19.23 $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( wal wi wex wb ax-gen 19.23t ax-mp ) BBCEFZCEABFCEACGBFHLCDIABCJK $.
      $( [1-Feb-2015] $) $( [5-Aug-1993] $)
  $}

  $( Theorem 19.7 of [Margaris] p. 89. $)
  alnex $p |- ( A. x -. ph <-> -. E. x ph ) $=
    ( wfal wi wal wex wn notfal pm2.21i 19.23 dfneg albii 3bitr4i ) ACDZBEABFZC
    DAGZBEOGACBCCBEHIJPNBAKLOKM $.
    $( [1-Feb-2015] $) $( [5-Aug-1993] $)

  $( Define existential quantification. ` E. x ph ` means "there exists at
     least one set ` x ` such that ` ph ` is true."  Definition of [Margaris]
     p. 49. $)
  df-ex $p |- ( E. x ph <-> -. A. x -. ph ) $=
    ( wn wal wex alnex con2bii ) ACBDABEABFG $.
    $( [2-Feb-2015] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Introduce equality axioms ax-8 through ax-14 except ax-9
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( --- Start of patch to prevent connective overloading $)
  $c class $.
  $( This syntax construction states that a variable ` x ` , which has been
     declared to be a set variable by $f statement vx, is also a class
     expression.  See comments in set.mm for justification.

     While it is tempting and perhaps occasionally useful to view ~ cv as a
     "type conversion" from a set variable to a class variable, keep in mind
     that ~ cv is intrinsically no different from any other class-building
     syntax.

     (The description above applies to set theory, not predicate calculus.  The
     purpose of introducing ` class x ` here, and not in set theory where it
     belongs, is to allow us to express i.e.  "prove" the ~ weq of predicate
     calculus from the ~ wceq of set theory, so that we don't "overload" the
     ` = ` connective with two syntax definitions.  This is done to prevent
     ambiguity that would complicate some Metamath parsers.) $)
  cv $a class x $.
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(          (None - the above patch had no old code.) $)
  $( --- End of old code before overloading prevention patch. $)

  $( Declare the equality predicate symbol. $)
  $c = $.  $( Equal sign (read:  'is equal to') $)

  $( --- Start of patch to prevent connective overloading $)
  ${
    $v A $.
    $v B $.
    wceq.cA $f class A $.
    wceq.cB $f class B $.
    $( Extend wff definition to include class equality.

       (The purpose of introducing ` wff A = B ` here, and not in set theory
       where it belongs, is to allow us to express i.e.  "prove" the ~ weq of
       predicate calculus in terms of the ~ wceq of set theory, so that we
       don't "overload" the ` = ` connective with two syntax definitions.  This
       is done to prevent ambiguity that would complicate some Metamath
       parsers.  For example, some parsers - although not the Metamath program
       - stumble on the fact that the ` = ` in ` x = y ` could be the ` = ` of
       either ~ weq or ~ wceq , although mathematically it makes no
       difference.  The class variables ` A ` and ` B ` are introduced
       temporarily for the purpose of this definition but otherwise not used in
       predicate calculus.) $)
    wceq $a wff A = B $.
  $}

  $( Extend wff definition to include atomic formulas using the equality
     predicate.

     (Instead of introducing ~ weq as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wceq .  This lets us avoid overloading
     the ` = ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ weq is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wceq .  Note:  To see the proof steps of this syntax proof, type "show
     proof weq /all" in the Metamath program.) $)
  weq $p wff x = y $=
    ( cv wceq ) ACBCD $.
    $( [24-Jan-2006] $)
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include atomic formulas using the equality
     predicate.

     After we introduce ~ cv and ~ wceq in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wceq". @)
  weq @a wff x = y @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Declare the membership predicate symbol. $)
  $c e. $. $( Stylized epsilon $)

  $( --- Start of patch to prevent connective overloading $)
  ${
    $v A $.
    $v B $.
    wcel.cA $f class A $.
    wcel.cB $f class B $.
    $( Extend wff definition to include the membership connective between
       classes.

       (The purpose of introducing ` wff A e. B ` here is to allow us to
       express i.e.  "prove" the ~ wel of predicate calculus in terms of the
       ~ wceq of set theory, so that we don't "overload" the ` e. ` connective
       with two syntax definitions.  This is done to prevent ambiguity that
       would complicate some Metamath parsers.  The class variables ` A ` and
       ` B ` are introduced temporarily for the purpose of this definition but
       otherwise not used in predicate calculus.) $)
    wcel $a wff A e. B $.
  $}

  $( Extend wff definition to include atomic formulas with the epsilon
     (membership) predicate.  This is read " ` x ` is an element of
     ` y ` ," " ` x ` is a member of ` y ` ," " ` x ` belongs to ` y ` ,"
     or " ` y ` contains ` x ` ."  Note:  The phrase " ` y ` includes
     ` x ` " means " ` x ` is a subset of ` y ` ;" to use it also for
     ` x e. y ` , as some authors occasionally do, is poor form and causes
     confusion, according to George Boolos (1992 lecture at MIT).

     This syntactical construction introduces a binary non-logical predicate
     symbol ` e. ` (epsilon) into our predicate calculus.  We will eventually
     use it for the membership predicate of set theory, but that is irrelevant
     at this point: the predicate calculus axioms for ` e. ` apply to any
     arbitrary binary predicate symbol.  "Non-logical" means that the predicate
     is presumed to have additional properties beyond the realm of predicate
     calculus, although these additional properties are not specified by
     predicate calculus itself but rather by the axioms of a theory (in our
     case set theory) added to predicate calculus.  "Binary" means that the
     predicate has two arguments.

     (Instead of introducing ~ wel as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wcel .  This lets us avoid overloading
     the ` e. ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ wel is considered to be a
     primitive syntax, even though here it is artificially "derived" from
     ~ wcel .  Note:  To see the proof steps of this syntax proof, type "show
     proof wel /all" in the Metamath program.) $)
  wel $p wff x e. y $=
    ( cv wcel ) ACBCD $.
    $( [24-Jan-2006] $)
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include atomic formulas with the epsilon
     (membership) predicate.  This is read " ` x ` is an element of ` y ` ,"
     " ` x ` is a member of ` y ` ," " ` x ` belongs to ` y ` ," or " ` y `
     contains ` x ` ."  Note:  The phrase " ` y ` includes ` x ` " means
     " ` x ` is a subset of ` y ` "; to use it also for ` x e. y ` (as some
     authors occasionally do) is poor form and causes confusion.

     After we introduce ~ cv and ~ wcel in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "vx cv vy cv wcel". @)
  wel @a wff x e. y @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Axiom of Equality.  One of the equality and substitution axioms of
     predicate calculus with equality.  This is similar to, but not quite, a
     transitive law for equality (proved later as ~ equtr ).  Axiom scheme C8'
     in [Megill] p. 448 (p. 16 of the preprint).  Also appears as Axiom C7 of
     [Monk2] p. 105.

     Axioms ~ ax-8 through ~ ax-16 are the axioms having to do with equality,
     substitution, and logical properties of our binary predicate ` e. ` (which
     later in set theory will mean "is a member of").  Note that all axioms
     except ~ ax-16 and ~ ax-17 are still valid even when ` x ` , ` y ` , and
     ` z ` are replaced with the same variable because they do not have any
     distinct variable (Metamath's $d) restrictions.  Distinct variable
     restrictions are required for ~ ax-16 and ~ ax-17 only. $)
  ax-8 $a |- ( x = y -> ( x = z -> y = z ) ) $.

  $( Axiom of Quantifier Substitution.  One of the equality and substitution
     axioms of predicate calculus with equality.  Appears as Lemma L12 in
     [Megill] p. 445 (p. 12 of the preprint).

     The original version of this axiom was ~ ax-10o ("o" for "old") and was
     replaced with this shorter ~ ax-10 in May 2008.  The old axiom is proved
     from this one as theorem ~ ax10o .  Conversely, this axiom is proved from
     ~ ax-10o as theorem ~ ax10 . $)
  ax-10 $a |- ( A. x x = y -> A. y y = x ) $.

  $( Axiom of Variable Substitution.  One of the 5 equality axioms of predicate
     calculus.  The final consequent ` A. x ( x = y -> ph ) ` is a way of
     expressing " ` y ` substituted for ` x ` in wff ` ph ` " (cf. ~ sb6 ).  It
     is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.

     The original version of this axiom was ~ ax-11o ("o" for "old") and was
     replaced with this shorter ~ ax-11 in Jan. 2007.  The old axiom is proved
     from this one as theorem ~ ax11o .  Conversely, this axiom is proved from
     ~ ax-11o as theorem ~ ax11 .

     Juha Arpiainen proved the independence of this axiom (in the form of the
     older axiom ~ ax-11o ) from the others on 19-Jan-2006.  See item 9a at
     ~ http://us.metamath.org/award2003.html .

     Interestingly, if the wff expression substituted for ` ph ` contains no
     wff variables, the resulting statement _can_ be proved without invoking
     this axiom.  This means that even though this axiom is _metalogically_
     independent from the others, it is not _logically_ independent.
     Specifically, we can prove any wff-variable-free instance of axiom
     ~ ax-11o (from which the ~ ax-11 instance follows by theorem ~ ax11 .)
     The proof is by induction on formula length, using ~ ax11eq and ~ ax11el
     for the basis steps and ~ ax11indn , ~ ax11indi , and ~ ax11inda for the
     induction steps.

     See also ~ ax11v and ~ ax11v2 for other equivalents of this axiom that
     (unlike this axiom) have distinct variable restrictions. $)
  ax-11 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.

  $( Axiom of Variable Substitution for Existence. This can be derived from
     ~ ax-11 in a classical context but a separate axiom is needed for
     intuitionistic predicate calculus. $)
  ax-i11e $a |- ( x = y -> ( E. y ph -> E. x ( x = y /\ ph ) ) ) $.

  $( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms of predicate calculus with equality.  Informally, it says that
     whenever ` z ` is distinct from ` x ` and ` y ` , and ` x = y ` is true,
     then ` x = y ` quantified with ` z ` is also true.  In other words, ` z `
     is irrelevant to the truth of ` x = y ` .  Axiom scheme C9' in [Megill]
     p. 448 (p. 16 of the preprint).  It apparently does not otherwise appear
     in the literature but is easily proved from textbook predicate calculus by
     cases.

     An open problem is whether this axiom is redundant.  Note that the
     analogous axiom for the membership connective, ~ ax-15 , has been shown to
     be redundant.  It is also unknown whether this axiom can be replaced by a
     shorter formula.  However, it can be derived from two slightly shorter
     formulas, as shown by ~ a12study .

     This axiom has been modified from the original ~ ax-12 for compatibility
     with intuitionistic logic. $)
  ax-i12 $a |- ( A. z z = x \/ ( A. z z = y \/
                 A. z ( x = y -> A. z x = y ) ) ) $.

  $( Axiom of Specialization.  A quantified wff implies the wff without a
     quantifier (i.e. an instance, or special case, of the generalized wff).
     In other words if something is true for all ` x ` , it is true for any
     specific ` x ` (that would typically occur as a free variable in the wff
     substituted for ` ph ` ).  (A free variable is one that does not occur in
     the scope of a quantifier: ` x ` and ` y ` are both free in ` x = y ` ,
     but only ` x ` is free in ` A. y x = y ` .)  This is one of the axioms of
     what we call "pure" predicate calculus ( ~ ax-4 through ~ ax-7 plus rule
     ~ ax-gen ).  Axiom scheme C5' in [Megill] p. 448 (p. 16 of the preprint).
     Also appears as Axiom B5 of [Tarski] p. 67 (under his system S2, defined
     in the last paragraph on p. 77).

     Note that the converse of this axiom does not hold in general, but a
     weaker inference form of the converse holds and is expressed as rule
     ~ ax-gen .  Conditional forms of the converse are given by ~ ax-12 ,
     ~ ax-15 , ~ ax-16 , and ~ ax-17 .

     Unlike the more general textbook Axiom of Specialization, we cannot choose
     a variable different from ` x ` for the special case.  For use, that
     requires the assistance of equality axioms, and we deal with it later
     after we introduce the definition of proper substitution - see ~ stdpc4 .

     An nice alternate axiomatization uses ~ ax467 and ~ ax-5o in place of
     ~ ax-4 , ~ ax-5 , ~ ax-6 , and ~ ax-7 .

     This axiom is redundant in the presence of certain other axioms, as shown
     by theorem ~ ax4 .  (We replaced the older ~ ax-5o and ~ ax-6o with newer
     versions ~ ax-5 and ~ ax-6 in order to prove this redundancy.) $)
  ax-4 $a |- ( A. x ph -> ph ) $.

  $( Rederive the original version of the axiom from ~ ax-i12 .  Note that we
     need ~ ax-4 for the derivation, but the proof of ~ ax4 is nontheless
     non-circular since it does not use ax-12.
     (Contributed by Mario Carneiro, 3-Feb-2015.) $)
  ax-12 $p |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x = y -> A. z x = y ) ) ) $=
    ( cv wceq wal wn wi wo ax-i12 ori ord ax-4 syl6 ) CDZADZECFZGZOBDZECFZGPSEZ
    UACFHZCFZUBRTUCQTUCIABCJKLUBCMN $.
    $( [3-Feb-2015] $)

  $( Derive the intuitionistic form of ~ ax-12 from the original form. $)
  ax12or $p |- ( A. z z = x \/ ( A. z z = y \/
                 A. z ( x = y -> A. z x = y ) ) ) $=
    ( ax-i12 ) ABCD $.
    $( [3-Feb-2015] $)

  $( Axiom of Equality.  One of the equality and substitution axioms for a
     non-logical predicate in our predicate calculus with equality.  It
     substitutes equal variables into the left-hand side of the ` e. ` binary
     predicate.  Axiom scheme C12' in [Megill] p. 448 (p. 16 of the preprint).
     It is a special case of Axiom B8 (p. 75) of system S2 of [Tarski] p. 77.
     "Non-logical" means that the predicate is not a primitive of predicate
     calculus proper but instead is an extension to it.  "Binary" means that
     the predicate has two arguments.  In a system of predicate calculus with
     equality, like ours, equality is not usually considered to be a
     non-logical predicate.  In systems of predicate calculus without equality,
     it typically would be. $)
  ax-13 $a |- ( x = y -> ( x e. z -> y e. z ) ) $.

  $( Axiom of Equality.  One of the equality and substitution axioms for a
     non-logical predicate in our predicate calculus with equality.  It
     substitutes equal variables into the right-hand side of the ` e. ` binary
     predicate.  Axiom scheme C13' in [Megill] p. 448 (p. 16 of the preprint).
     It is a special case of Axiom B8 (p. 75) of system S2 of [Tarski]
     p. 77. $)
  ax-14 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof uses only ~ ax-5 ,
     ~ ax-8 , ~ ax-12 , and ~ ax-gen .  This shows that this can be proved
     without ~ ax-9 , even though the theorem ~ equid cannot be.  A shorter
     proof using ~ ax-9 is obtainable from ~ equid and ~ hbth .)  (The proof
     was shortened by Wolf Lammen, 23-Mar-2014.) $)
  hbequid $p |- ( x = x -> A. y x = x ) $=
    ( cv wceq wal wi wo ax12or ax-8 pm2.43i alimi a1d ax-4 jaoi ax-mp ) BCACZDZ
    BEZRPPDZSBEZFZBEZGZGUAAABHRUAUCRTSQSBQSBAAIJKLZRUAUBUDUABMNNO $.
    $( [3-Feb-2015] $) $( [13-Jan-2011] $)

  $( Obsolete proof of ~ hbequid as of 23-Mar-2014. $)
  hbequidOLD $p |- ( x = x -> A. y x = x ) $=
    ( cv wceq wal wi ax-12 ax-8 pm2.43i ax-gen ax-5 ax-mp a1d pm2.61ii ) BCACZD
    ZBEZQOODZRBEZFAABGQSRPRFZBEQSFTBPRBAAHIJPRBKLMZUAN $.
    $( [13-Jan-2011] $)

  $( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint). $)
  alequcom $p |- ( A. x x = y -> A. y y = x ) $=
    ( ax-10 ) ABC $.
    $( [5-Aug-1993] $)

  ${
    alequcoms.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers. $)
    alequcoms $p |- ( A. y y = x -> ph ) $=
      ( weq wal alequcom syl ) CBECFBCEBFACBGDH $.
      $( [5-Aug-1993] $)
  $}

  ${
    nalequcoms.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.
       (Revised by Mario Carneiro, 2-Feb-2015.) $)
    nalequcoms $p |- ( -. A. y y = x -> ph ) $=
      ( cv wceq wal wn alequcom con3i syl ) CEZBEZFCGZHMLFBGZHAONBCIJDK $.
      $( [2-Feb-2015] $) $( [2-Jan-2002] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom ax-17 - first use of the $d distinct variable statement
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ph $.
    $( Axiom to quantify a variable over a formula in which it does not occur.
       Axiom C5 in [Megill] p. 444 (p. 11 of the preprint).  Also appears as
       Axiom B6 (p. 75) of system S2 of [Tarski] p. 77 and Axiom C5-1 of
       [Monk2] p. 113.

       This axiom is _logically_ redundant in the (logically complete)
       predicate calculus axiom system consisting of ~ ax-gen , ~ ax-4 through
       ~ ax-9 , ~ ax-10o , and ~ ax-12 through ~ ax-16 : in that system, we can
       derive any instance of ~ ax-17 not containing wff variables by induction
       on formula length, using ~ ax17eq and ~ ax17el for the basis together
       ~ hbn , ~ hbal , and ~ hbim .  However, if we omit this axiom, our
       development would be quite inconvenient since we could work only with
       specific instances of wffs containing no wff variables - this axiom
       introduces the concept of a set variable not occurring in a wff (as
       opposed to just two set variables being distinct). $)
    ax-17 $a |- ( ph -> A. x ph ) $.
  $}

  ${
    $d x ps $.
    $( ~ ax-17 with antecedent. $)
    a17d $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wal wi ax-17 a1i ) BBCDEABCFG $.
      $( [1-Mar-2013] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive ax-9 from a weaker version
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    $d x w $.  $d w z $.
    a9wa9lem1.1 $e |- -. A. w -. w = x $.
    $( Lemma for ~ a9wa9 .  Similar to ~ equcomi , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem1 $p |- ( x = y -> y = x ) $=
      ( weq wn wal ax-8 pm2.43i con3i alimi mto ax-17 mt3 mpi ) ABEAAEZBAEPPFZC
      GZRCAEZFZCGDQTCSPSPCAAHIJKLQCMNABAHO $.
      $( [12-Nov-2013] $)

    a9wa9lem2.2 $e |- -. A. w -. w = z $.
    $( Lemma for ~ a9wa9 .  Similar to ~ equequ2 , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
      ( weq a9wa9lem1 ax-8 com12 syl5 syl2im impbid ) ABGZCAGZCBGZOACGZNPCADFHQ
      NPACBIJKNBAGZPBCGZOABDEHCBDFHSROBCAIJLM $.
      $( [3-Apr-2014] $) $( [12-Nov-2013] $)

    $( Obsolete proof of ~ a9wa9lem2 as of 3-Apr-2014. $)
    a9wa9lem2OLD $p |- ( x = y -> ( z = x <-> z = y ) ) $=
      ( weq wi a9wa9lem1 ax-8 syl com12 syl2im impbid ) ABGZCAGZCBGZPOQPACGOQHC
      ADFIACBJKLOBAGZQBCGZPABDEICBDFISRPBCAJLMN $.
      $( [12-Nov-2013] $)
  $}

  ${
    $d x w $.  $d w ph $.
    a9wa9lem3.1 $e |- -. A. w -. w = x $.
    a9wa9lem3.2 $e |- -. A. x -. x = w $.
    $( Lemma for ~ a9wa9 .  Similar to ~ ax4 , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem3 $p |- ( A. x ph -> ph ) $=
      ( wal wi weq wn ax-17 a9wa9lem1 ax-11 syl2im con2 al2imi mtoi con4d con3i
      syl6 alrimi mt3 ) ABFZAGZCBHZIZCFDUCIZUECUFCJUDUCUDAUBUDAIZBCHZUGGZBFZUBI
      UDUHUGUGCFUJCBBEKUGCJUGBCLMUJUBUHIZBFEUIAUKBUHANOPSQRTUA $.
      $( [12-Nov-2013] $)

    $( Lemma for ~ a9wa9 .  Similar to ~ hba1 , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem4 $p |- ( A. x ph -> A. x A. x ph ) $=
      ( wal wn a9wa9lem3 con2i ax-6 con1i alimi 3syl ) ABFZNGZBFZGZQBFNBFPNOBCD
      EHIOBJQNBNPABJKLM $.
      $( [12-Nov-2013] $)

    a9wa9lem5.3 $e |- ( ph -> A. x ph ) $.
    $( Lemma for ~ a9wa9 .  Similar to ~ hbn , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem5 $p |- ( -. ph -> A. x -. ph ) $=
      ( wn wal a9wa9lem3 con3i ax-6 alrimi syl ) AGZABHZGZNBHOAABCDEIJPNBABKAOF
      JLM $.
      $( [12-Nov-2013] $)
  $}

  ${
    $d x w $.  $d w ph $.  $d w ps $.
    a9wa9lem6.1 $e |- -. A. w -. w = x $.
    a9wa9lem6.2 $e |- -. A. x -. x = w $.
    a9wa9lem6.3 $e |- ( ph -> A. x ph ) $.
    a9wa9lem6.4 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    a9wa9lem6.5 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Lemma for ~ a9wa9 .  Similar to ~ hbimd , without using ~ ax-9 or
       ~ ax-4 .  (The proof was shortened by Wolf Lammen, 3-Apr-2014.) $)
    a9wa9lem6 $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi wal wn alrimi a9wa9lem3 ax-6 nsyl4 con1i alimi syl6 con3 al2imi ax-1
      syl2im pm2.21 jad ) ABCBCKZDLZABMZUIDLZUHABBDLZKZDLUIUKMZDLZUJAULDHINUNBU
      KBUNBDEFGOBDPQRULUMUIDBUKUAUBUDUIUGDBCUESTACCDLUHJCUGDCBUCSTUF $.
      $( [3-Apr-2014] $) $( [12-Nov-2013] $)

    $( Obsolete proof of ~ a9wa9lem6 as of 3-Apr-2014. $)
    a9wa9lem6OLD $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi wal wn alrimi a9wa9lem3 ax-6 nsyl4 con1i alimi syl6com al2imi syl2im
      con3 pm2.21 ax-1 ja com12 ) BCKZAUHDLZBCAUIKABMZUJDLZUIABBDLZKZDLUJULMZDL
      ZUKAUMDHINUOBULBUOBDEFGOBDPQRUMUNUJDBULUCUAUBUJUHDBCUDSTACCDLUIJCUHDCBUES
      TUFUG $.
      $( [12-Nov-2013] $)
  $}

  ${
    $d x w $.  $d w ph $.  $d w ps $.
    a9wa9lem7.1 $e |- -. A. w -. w = x $.
    a9wa9lem7.2 $e |- -. A. x -. x = w $.
    a9wa9lem7.3 $e |- ( ph -> A. x ph ) $.
    a9wa9lem7.4 $e |- ( ps -> A. x ps ) $.
    $( Lemma for ~ a9wa9 .  Similar to ~ hban , without using ~ ax-9 or
       ~ ax-4 . $)
    a9wa9lem7 $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
      ( wa wn wi df-an wal a9wa9lem5 pm2.21 alrimi ax-1 ja hbxfrbi ) ABIABJZKZJ
      CABLUACDEFATUACMAJUACACDEFGNATOPTUACBCDEFHNTAQPRNS $.
      $( [12-Nov-2013] $)
  $}

  ${
    $d x v w z $.  $d y v w z $.  $d w x ph $.  $d w z ps $.
    a9wa9.1 $e |- -. A. w -. w = x $.
    a9wa9.2 $e |- -. A. x -. x = w $.
    a9wa9.3 $e |- -. A. z -. z = y $.
    a9wa9.4 $e |- -. A. w -. w = z $.
    a9wa9.5 $e |- -. A. z -. z = w $.

    ${
      a9wa9lem8.6 $e |- ( z = y -> ( ph <-> ps ) ) $.
      $( Lemma for ~ a9wa9 .  Similar to ~ dvelimfALT , without using ~ ax-9 or
         ~ ax-4 .  (The proof was shortened by Wolf Lammen, 18-Jul-2014.) $)
      a9wa9lem8 $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
        ( weq wal wn wi ax-17 alrimi alimi ax-6 a1d a9wa9lem3 syl5ibr a2i ax-10
        wa syl con3i nalequcoms a9wa9lem7 ax-12 imp a17d a9wa9lem6 hbald biimpd
        con3 al2imi mtoi con1i 3syl syl56 expcom ax-11 syl2im pm2.27 pm2.61d2
        syld ) CDMZCNOZCEMZCNZBBCNZPZVLOZVJVNBEDMZAPZENZVOVJUFZVRCNVMBVPBENZPZE
        NVRBWAEBEQZBVTVPWBUARWAVQEVPVTAVTAVPBBEFJKUBLUCUDSUGVSVQCEVOVJEFJKVOENE
        CECMZENZOVOEWCETVLWDCEUEUHRUIVJEQUJVSVPACFGHVOVJCFGHVKCTVICTUJVOVJVPVPC
        NPEDCUKULVSACUMUNUOVRBCVRVPBPZENZBOZENZOBVQWEEVPABVPABLUPUDSWFWHVPOZENI
        WEWGWIEVPBUQURUSBWHWGEQUTVASVBVCVLBVKBPZCNZVMVLVKBVTWKVKCFGHUBWBBCEVDVE
        VKWJBCVKBVFURVHVG $.
        $( [18-Jul-2014] $) $( [12-Nov-2013] $)

      $( Obsolete proof of ~ a9wa9lem8 as of 18-Jul-2014. $)
      a9wa9lem8OLD $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
        ( weq wi wal wn ax-17 a1d alimi ax-6 alrimi a9wa9lem3 syl5ibr a9wa9lem4
        a2i syl ax-11 pm2.27 al2imi syld ax-10 con3i nalequcoms a9wa9lem7 ax-12
        syl5 wa imp a17d a9wa9lem6 hbald ex pm2.61i biimpd con3 mtoi con1i 3syl
        syl56 ) BEDMZANZEOZCDMZCOPZVLCOZBCOBVJBEOZNZEOVLBVQEBEQZBVPVJVRRUAVQVKE
        VJVPAVPAVJBBEFJKUBLUCUESUFCEMZCOZVNVLVONZNVTWAVNVLVLEOZVTVOVKEFJKUDVTWB
        VSVLNZCOZVOVTVSWBWDNVSCFGHUBVLCEUGUFVSWCVLCVSVLUHUIUJUPRVTPZVNWAWEVNUQZ
        VKCEWEVNEFJKWEEOECECMZEOZPWEEWGETVTWHCEUKULUAUMVNEQUNWFVJACFGHWEVNCFGHV
        SCTVMCTUNWEVNVJVJCONEDCUOURWFACUSUTVAVBVCVLBCVLVJBNZEOZBPZEOZPBVKWIEVJA
        BVJABLVDUESWJWLVJPZEOIWIWKWMEVJBVEUIVFBWLWKEQVGVHSVI $.
        $( [12-Nov-2013] $)
    $}

    a9wa9.6 $e |- -. A. v -. v = y $.
    a9wa9.7 $e |- -. A. w -. w = v $.
    a9wa9.8 $e |- -. A. x -. x = v $.
    $( Derive ~ ax-9 (which has no distinct variable requirement) from a weaker
       version that requires that its two variables be distinct.  The
       hypotheses are the instances of the weaker version that we need.
       Neither ~ ax-9 nor ~ ax-4 (which can be derived from ~ ax-9 ) is used by
       the proof.  Note that every other predicate calculus axiom (except
       ~ ax-13 and ~ ax-14 ) is used by the proof.  (The proof was shortened by
       Wolf Lammen, 28-Mar-2014.) $)
    a9wa9 $p |- -. A. x -. x = y $=
      ( weq wal wn a9wa9lem3 nsyl3 wi a9wa9lem2 ax-17 a9wa9lem8 a9wa9lem4 albid
      wb syl notbid mtbii syl6com con3i alrimi mt3 pm2.61i ) ABNZAOZUNPZAOZPZUQ
      UNUOUPADFGQUNADFGQRUOPZURSZEBNZPZEOKUTPZVBEVCEUAVAUTUSVAVAAOZURECNVAABCDF
      GHIJCBEDILTUBVDAENZPZAOUQMVDVFUPAVAADFGUCVDVEUNVDVAVEUNUEVAADFGQEBADLFTUF
      UGUDUHUIUJUKULUM $.
      $( [28-Mar-2014] $) $( [12-Nov-2013] $)

    $( Obsolete proof of ~ a9wa9 as of 28-Mar-2014. $)
    a9wa9OLD $p |- -. A. x -. x = y $=
      ( cv wceq wal wn a9wa9lem3 syl a9wa9lem2 con2i a9wa9lem8 a9wa9lem4 notbid
      wi ax-17 wb albid mpbii syl6com con3i alrimi mt3 pm2.61i ) ANZBNZOZAPZUQQ
      ZAPZQZURUQVAUQADFGRUTUQUSADFGRUASURQZVAUEZENZUPOZQZEPKVCQZVFEVGEUFVEVCVBV
      EVEAPZVAVDCNOVEABCDFGHIJCBEDILTUBVHUOVDOZQZAPZQVAMVHVKUTVHVJUSAVEADFGUCVH
      VIUQVHVEVIUQUGVEADFGREBADLFTSUDUHUDUIUJUKULUMUN $.
      $( [12-Nov-2013] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Introduce Axiom of Existence ax-9
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Existence.  One of the equality and substitution axioms of
     predicate calculus with equality.  One thing this axiom tells us is that
     at least one thing exists (although ~ ax-4 and possibly others also tell
     us that, i.e. they are not valid in the empty domain of a "free logic").
     In this form (not requiring that ` x ` and ` y ` be distinct) it was used
     in an axiom system of Tarski (see Axiom B7' in footnote 1 of
     [KalishMontague] p. 81.)  It is equivalent to axiom scheme C10' in
     [Megill] p. 448 (p. 16 of the preprint); the equivalence is established by
     ~ ax9o and ~ ax9 .  A more convenient form of this axiom is ~ a9e , which
     has additional remarks.

     Raph Levien proved the independence of this axiom from the other logical
     axioms on 12-Apr-2005.  See item 16 at
     ~ http://us.metamath.org/award2003.html .

     ~ ax-9 can be proved from a weaker version requiring that the variables be
     distinct; see theorem ~ a9wa9 . $)
  ax-i9 $a |- E. x x = y $.

  $( Derive ~ ax-9 from ~ ax-i9 , the modified version for intuitionistic
     logic. $)
  ax-9 $p |- -. A. x -. x = y $=
    ( cv wceq wn wal wex ax-i9 notnoti alnex mtbir ) ACBCDZEAFLAGZEMABHILAJK $.
    $( [3-Feb-2015] $)

  $( ~ equid with existential quantifier without using ~ ax-4 or ~ ax-17 .
     (The proof was shortened by Wolf Lammen, 27-Feb-2014.) $)
  equidqe $p |- -. A. y -. x = x $=
    ( weq wn wal ax-9 ax-8 pm2.43i con3i alimi mto ) AACZDZBEBACZDZBEBAFMOBNLNL
    BAAGHIJK $.
    $( [27-Feb-2014] $) $( [13-Jan-2011] $)

  $( Obsolete proof of ~ equidqe as of 27-Feb-2014. $)
  equidqeOLD $p |- -. A. y -. x = x $=
    ( weq wn wal ax-9 wi ax-8 pm2.43i con3i ax-gen ax-5 ax-mp mto ) AACZDZBEZBA
    CZDZBEZBAFPSGZBEQTGUABROROBAAHIJKPSBLMN $.
    $( [13-Jan-2011] $)

  $( ~ equid with universal quantifier without using ~ ax-4 or ~ ax-17 . $)
  equidq $p |- A. y x = x $=
    ( weq wal wn equidqe ax-6 hbequid con3i alrimi mt3 ) AACZBDZLEZBDABFMENBLBG
    LMABHIJK $.
    $( [13-Jan-2011] $)

  $( A special case of ~ ax-4 without using ~ ax-4 or ~ ax-17 . $)
  ax4sp1 $p |- ( A. y -. x = x -> -. x = x ) $=
    ( weq wn wal equidqe pm2.21i ) AACDZBEHABFG $.
    $( [13-Jan-2011] $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive ax-4, ax-5o, and ax-6o
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.  $d y ph $.
    $( Theorem showing that ~ ax-4 can be derived from ~ ax-5 , ~ ax-gen ,
       ~ ax-8 , ~ ax-9 , ~ ax-11 , and ~ ax-17 and is therefore redundant in a
       system including these axioms.  The proof uses ideas from the proof of
       Lemma 21 of [Monk2] p. 114.

       This theorem should not be referenced in any proof.  Instead, we will
       use ~ ax-4 below so that explicit uses of ~ ax-4 can be more easily
       identified.  In particular, this will more cleanly separate out the
       theorems of "pure" predicate calculus that don't involve equality or
       distinct variables.  A beginner may wish to accept ~ ax-4 a priori, so
       that the proof of this theorem ( ~ ax4 ), which involves equality as
       well as the distinct variable requirements of ~ ax-17 , can be put off
       until those axioms are studied.

       Note:  All predicate calculus axioms introduced from this point forward
       are redundant.  Immediately before their introduction, we prove them
       from earlier axioms to demonstrate their redundancy.  Specifically,
       redundant axioms ~ ax-4 , ~ ax-5o , ~ ax-6o , ~ ax-9o , ~ ax-10o ,
       ~ ax-11o , ~ ax-15 , and ~ ax-16 are proved by theorems ~ ax4 , ~ ax5o ,
       ~ ax6o , ~ ax9o , ~ ax10o , ~ ax11o , ~ ax15 , and ~ ax16 .  Except for
       the ones suffixed with o ( ~ ax-5o etc.), we never reference those
       theorems directly.  Instead, we use the axiom version that immediately
       follows it.  This allow us to better isolate the uses of the redundant
       axioms for easier study of subsystems containing them.

       (The proof was shortened by Scott Fenton, 24-Jan-2011.) $)
    ax4 $p |- ( A. x ph -> ph ) $=
      ( vy wal wi weq ax-9 ax-8 pm2.43i con3i ax-gen ax-17 ax-5 mpsyl mt3 ax-11
      wn mpi syl2im con2 ax-mp syl mtoi syl6 con4d ) ABDZAEZCBFZQZCDZCBGUGQZUIE
      ZCDUKUKCDUJULCUHUGUHAUFUHAQZBCFZUMEZBDZUFQUHUNUMUMCDUPUHCCFZUNUQUNQZBDZBC
      GZUQQZUREZBDVAVABDUSVBBUNUQUNUQBCCHIJKVABLVAURBMNOCBCHRUMCLUMBCPSUPUFUSUT
      UPAUREZBDZUFUSEUOVCEZBDUPVDEVEBUNATKUOVCBMUAAURBMUBUCUDUEJKUKCLUKUICMNO
      $.
      $( [24-Jan-2011] $) $( [21-May-2008] $)
  $}

  $( Show that the original axiom ~ ax-5o can be derived from ~ ax-5 and
     others.  See ~ ax5 for the rederivation of ~ ax-5 from ~ ax-5o .

     Part of the proof is based on the proof of Lemma 22 of [Monk2] p. 114.

     Normally, ~ ax5o should be used rather than ~ ax-5o , except by theorems
     specifically studying the latter's properties. $)
  ax5o $p |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wal wi wn ax-4 con2i ax-6 con1i ax-gen ax-5 ax-mp 3syl syl5 ) ACDZPCDZPBE
    CDBCDPPFZCDZFZTCDZQSPRCGHRCITPEZCDUAQEUBCPSACIJKTPCLMNPBCLO $.
    $( [21-May-2008] $)

  $( Axiom of Quantified Implication.  This axiom moves a quantifier from
     outside to inside an implication, quantifying ` ps ` .  Notice that ` x `
     must not be a free variable in the antecedent of the quantified
     implication, and we express this by binding ` ph ` to "protect" the axiom
     from a ` ph ` containing a free ` x ` .  One of the 4 axioms of "pure"
     predicate calculus.  Axiom scheme C4' in [Megill] p. 448 (p. 16 of the
     preprint).  It is a special case of Lemma 5 of [Monk2] p. 108 and Axiom 5
     of [Mendelson] p. 69.

     This axiom is redundant, as shown by theorem ~ ax5o .

     Normally, ~ ax5o should be used rather than ~ ax-5o , except by theorems
     specifically studying the latter's properties. $)
  ax-5o $a |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Rederivation of axiom ~ ax-5 from the orginal version, ~ ax-5o .  See
     ~ ax5o for the derivation of ~ ax-5o from ~ ax-5 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-5
     above so that uses of ~ ax-5 can be more easily identified.

     Note:  This is the same as theorem ~ alim below.  It is proved separately
     here so that it won't be dependent on the axioms used for ~ alim . $)
  ax5 $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wi wal ax-4 syl5 ax-gen ax-5o ax-mp syl ) ABDZCEZACEZBDZCEZNBCEDMODZCEMPD
    QCNAMBACFLCFGHLOCIJABCIK $.
    $( [5-Dec-2010] $) $( [23-May-2008] $)

  $( Show that the original axiom ~ ax-6o can be derived from ~ ax-6 and
     others.  See ~ ax6 for the rederivation of ~ ax-6 from ~ ax-6o .

     Normally, ~ ax6o should be used rather than ~ ax-6o , except by theorems
     specifically studying the latter's properties. $)
  ax6o $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn ax-4 ax-6 nsyl4 ) ABCZAHDBCABEABFG $.
    $( [21-May-2008] $)

  $( Axiom of Quantified Negation.  This axiom is used to manipulate negated
     quantifiers.  One of the 4 axioms of pure predicate calculus.  Equivalent
     to axiom scheme C7' in [Megill] p. 448 (p. 16 of the preprint).  An
     alternate axiomatization could use ~ ax467 in place of ~ ax-4 , ~ ax-6o ,
     and ~ ax-7 .

     This axiom is redundant, as shown by theorem ~ ax6o .

     Normally, ~ ax6o should be used rather than ~ ax-6o , except by theorems
     specifically studying the latter's properties. $)
  ax-6o $a |- ( -. A. x -. A. x ph -> ph ) $.

  $( Rederivation of axiom ~ ax-6 from the orginal version, ~ ax-6o .  See
     ~ ax6o for the derivation of ~ ax-6o from ~ ax-6 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-6
     above so that uses of ~ ax-6 can be more easily identified. $)
  ax6 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( wal wn wi ax-4 id ax-gen ax-5o ax-mp nsyl ax-6o nsyl4 ) ABCZBCZDZBCZNDZBC
    ZNQREZBCQSETBQONPBFNNEZBCNOEUABNGHANBIJKHPRBIJNBLM $.
    $( [23-May-2008] $)

  $( ` x ` is not free in ` A. x ph ` .
     Axiom 7 of 10 for intuitionistic logic. $)
  ax-ial $a |- ( A. x ph -> A. x A. x ph ) $.

  $( The converse of ~ ax-5o .
     Axiom 8 of 10 for intuitionistic logic. $)
  ax-i5r $a |- ( ( A. x ph -> A. x ps ) -> A. x ( A. x ph -> ps ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    "Pure" predicate calculus including ax-4, without distinct variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    a4i.1 $e |- A. x ph $.
    $( Inference rule reversing generalization. $)
    a4i $p |- ph $=
      ( wal ax-4 ax-mp ) ABDACABEF $.
      $( [5-Aug-1993] $)
  $}

  ${
    a4s.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent. $)
    a4s $p |- ( A. x ph -> ps ) $=
      ( wal ax-4 syl ) ACEABACFDG $.
      $( [5-Aug-1993] $)
  $}

  ${
    a4sd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction generalizing antecedent. $)
    a4sd $p |- ( ph -> ( A. x ps -> ch ) ) $=
      ( wal ax-4 syl5 ) BDFBACBDGEH $.
      $( [17-Aug-1994] $)
  $}

  $( Closed theorem version of bound-variable hypothesis builder ~ hbn . $)
  hbnt $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $=
    ( wn wal wi ax-4 con3i ax-6 syl con3 al2imi syl5 ) ACZABDZCZBDZANEZBDMBDMOP
    NAABFGABHIQOMBANJKL $.
    $( [2-Feb-2015] $) $( [5-Aug-1993] $)

  $( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114. $)
  hba1 $p |- ( A. x ph -> A. x A. x ph ) $=
    ( ax-ial ) ABC $.
    $( [5-Aug-1993] $)

  ${
    a5i.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ ax-5o . $)
    a5i $p |- ( A. x ph -> A. x ps ) $=
      ( wal wi hba1 ax-5 syl5 mpg ) ACEZBFZKBCEZFCKKCELCEMACGKBCHIDJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    hb.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` . $)
    hbn $p |- ( -. ph -> A. x -. ph ) $=
      ( wal wi wn hbnt mpg ) AABDEAFZIBDEBABGCH $.
      $( [5-Aug-1993] $)

    hb.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (The proof was shortened by O'Cat, 3-Mar-2008.)
       (Revised by Mario Carneiro, 2-Feb-2015.) $)
    hbim $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wi wal ax-4 imim12i ax-i5r imim1i alimi 3syl ) ABFZACGZBCGZFOBFZCGNCGOA
      BPACHEIABCJQNCAOBDKLM $.
      $( [2-Feb-2015] $) $( [5-Aug-1993] $)

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph \/ ps ) ` . $)
    hbor $p |- ( ( ph \/ ps ) -> A. x ( ph \/ ps ) ) $=
      ( wo wal orc alimi syl olc jaoi ) AABFZCGZBAACGNDAMCABHIJBBCGNEBMCBAKIJL
      $.
      $( [2-Feb-2015] $) $( [5-Aug-1993] $)

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .
       (The proof was shortened by Mario Carneiro, 2-Feb-2015.) $)
    hban $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
      ( wa wal anim12i 19.26 sylibr ) ABFZACGZBCGZFKCGALBMDEHABCIJ $.
      $( [2-Feb-2015] $) $( [5-Aug-1993] $)

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph <-> ps ) ` . $)
    hbbi $p |- ( ( ph <-> ps ) -> A. x ( ph <-> ps ) ) $=
      ( wb wi wa dfbi2 hbim hban hbxfrbi ) ABFABGZBAGZHCABIMNCABCDEJBACEDJKL
      $.
      $( [5-Aug-1993] $)

    hb.3 $e |- ( ch -> A. x ch ) $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not
       free in ` ( ph \/ ps \/ ch ) ` . $)
    hb3or $p |- ( ( ph \/ ps \/ ch ) -> A. x ( ph \/ ps \/ ch ) ) $=
      ( w3o wo df-3or hbor hbxfrbi ) ABCHABIZCIDABCJMCDABDEFKGKL $.
      $( [14-Sep-2003] $)

    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not
       free in ` ( ph /\ ps /\ ch ) ` . $)
    hb3an $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $=
      ( w3a wa df-3an hban hbxfrbi ) ABCHABIZCIDABCJMCDABDEFKGKL $.
      $( [14-Sep-2003] $)
  $}

  $( Lemma 24 of [Monk2] p. 114. $)
  hba2 $p |- ( A. y A. x ph -> A. x A. y A. x ph ) $=
    ( wal hba1 hbal ) ABDBCABEF $.
    $( [29-May-2008] $)

  $( Lemma 23 of [Monk2] p. 114. $)
  hbia1 $p |- ( ( A. x ph -> A. x ps ) -> A. x ( A. x ph -> A. x ps ) ) $=
    ( wal hba1 hbim ) ACDBCDCACEBCEF $.
    $( [29-May-2008] $)

  $( Obsolete proof of ~ hbn1 as of 15-Aug-2014. $)
  hbn1OLD $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( wal hba1 hbn ) ABCBABDE $.
    $( [5-Aug-1993] $)

  $( ` x ` is not free in ` -. A. x ph ` .  (The proof was shortened by Wolf
     Lammen, 18-Aug-2014.) $)
  hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( ax-6 ) ABC $.
    $( [18-Aug-2014] $) $( [5-Aug-1993] $)

  $( Proof of a single axiom that can replace ~ ax-4 and ~ ax-6o .  See
     ~ ax46to4 and ~ ax46to6 for the re-derivation of those axioms.
     (Contributed by Scott Fenton, 12-Sep-2005.) $)
  ax46 $p |- ( ( A. x -. A. x ph -> A. x ph ) -> ph ) $=
    ( wal wn ax-6o ax-4 ja ) ABCZDBCHAABEABFG $.
    $( [12-Sep-2005] $)

  $( Re-derivation of ~ ax-4 from ~ ax46 .  Only propositional calculus is used
     for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.) $)
  ax46to4 $p |- ( A. x ph -> ph ) $=
    ( wal wn wi ax-1 ax46 syl ) ABCZIDBCZIEAIJFABGH $.
    $( [12-Sep-2005] $)

  $( Re-derivation of ~ ax-6o from ~ ax46 .  Only propositional calculus is
     used for the re-derivation.  (Contributed by Scott Fenton,
     12-Sep-2005.) $)
  ax46to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn wi pm2.21 ax46 syl ) ABCZDBCZDJIEAJIFABGH $.
    $( [12-Sep-2005] $)

  $( Proof of a single axiom that can replace both ~ ax-6o and ~ ax-7 .  See
     ~ ax67to6 and ~ ax67to7 for the re-derivation of those axioms. $)
  ax67 $p |- ( -. A. x -. A. y A. x ph -> A. y ph ) $=
    ( wal wn ax-7 con3i alimi ax-6o syl ) ABDCDZEZBDZEACDZBDZEZBDZENQMPLBKOACBF
    GHGNBIJ $.
    $( [18-Nov-2006] $)

  $( Re-derivation of ~ ax-6o from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation. $)
  ax67to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn hba1 con3i alimi ax67 ax-4 3syl ) ABCZDZBCZDKBCZDZBCZDKAPMOLBKNABE
    FGFABBHABIJ $.
    $( [18-Nov-2006] $)

  $( Re-derivation of ~ ax-7 from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation. $)
  ax67to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wn ax67to6 con4i ax67 alimi syl ) ACDBDZKEZCDEZCDZABDZCDNKLCFGMOCACBH
    IJ $.
    $( [18-Nov-2006] $)

  $( Proof of a single axiom that can replace ~ ax-4 , ~ ax-6o , and ~ ax-7 in
     a subsystem that includes these axioms plus ~ ax-5o and ~ ax-gen (and
     propositional calculus).  See ~ ax467to4 , ~ ax467to6 , and ~ ax467to7 for
     the re-derivation of those axioms.  This theorem extends the idea in Scott
     Fenton's ~ ax46 . $)
  ax467 $p |- ( ( A. x A. y -. A. x A. y ph -> A. x ph ) -> ph ) $=
    ( wal wn ax-4 hbn1 ax-6o con1i alimi ax-7 3syl nsyl4 ja ) ACDZBDEZCDBDZABDA
    OAQACFOEZRCDPBDZCDQACGRSCSOOBHIJPCBKLMABFN $.
    $( [18-Nov-2006] $)

  $( Re-derivation of ~ ax-4 from ~ ax467 .  Only propositional calculus is
     used by the re-derivation. $)
  ax467to4 $p |- ( A. x ph -> ph ) $=
    ( wal wn wi ax-1 ax467 syl ) ABCZIBCDBCBCZIEAIJFABBGH $.
    $( [19-Nov-2006] $)

  $( Re-derivation of ~ ax-6o from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 . $)
  ax467to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn wi ax467to4 hba1 con3i alimi syl pm2.21 ax467 3syl ) ABCZDZBCZDNBC
    ZDZBCZBCZDTNEATPTSPSBFROBNQABGHIJHTNKABBLM $.
    $( [19-Nov-2006] $)

  $( Re-derivation of ~ ax-7 from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 . $)
  ax467to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wn ax467to6 con4i wi pm2.21 ax467 syl alimi nsyl4 ) ACDBDZNEZCDZEZCDZ
    ABDZCDRNOCFGQSCPBDZEZBDSPUAABUATSHATSIABCJKLPBFMLK $.
    $( [19-Nov-2006] $)

  $( The analog in our "pure" predicate calculus of axiom 5 of modal logic
     S5. $)
  modal-5 $p |- ( -. A. x -. ph -> A. x -. A. x -. ph ) $=
    ( wn hbn1 ) ACBD $.
    $( [5-Oct-2005] $)

  $( The analog in our "pure" predicate calculus of the Brouwer axiom (B) of
     modal logic S5. $)
  modal-b $p |- ( ph -> A. x -. A. x -. ph ) $=
    ( wn wal ax6o con4i ) ACZBDCBDAGBEF $.
    $( [5-Oct-2005] $)

  ${
    19.3.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be quantified with a variable not free in it.  Theorem 19.3 of
       [Margaris] p. 89. $)
    19.3 $p |- ( A. x ph <-> ph ) $=
      ( wal ax-4 impbii ) ABDAABECF $.
      $( [21-May-2007] $) $( [5-Aug-1993] $)
  $}

  ${
    19.16.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.16 of [Margaris] p. 90. $)
    19.16 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) ) $=
      ( wal wb 19.3 albi syl5bbr ) AACEABFCEBCEACDGABCHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.17.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.17 of [Margaris] p. 90. $)
    19.17 $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) ) $=
      ( wb wal albi 19.3 syl6bb ) ABECFACFBCFBABCGBCDHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.21.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ." $)
    19.21 $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wi wal alim syl5 hba1 hbim ax-4 imim2i alrimi impbii ) ABEZCFZABCFZEZAA
      CFPQDABCGHROCAQCDBCIJQBABCKLMN $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.21-2.1 $e |- ( ph -> A. x ph ) $.
    19.21-2.2 $e |- ( ph -> A. y ph ) $.
    $( Theorem 19.21 of [Margaris] p. 90 but with 2 quantifiers. $)
    19.21-2 $p |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) ) $=
      ( wi wal 19.21 albii bitri ) ABGDHZCHABDHZGZCHAMCHGLNCABDFIJAMCEIK $.
      $( [4-Feb-2005] $)
  $}

  ${
    stdpc5.1 $e |- ( ph -> A. x ph ) $.
    $( An axiom scheme of standard predicate calculus that emulates Axiom 5 of
       [Mendelson] p. 69.  The hypothesis ` ( ph -> A. x ph ) ` can be thought
       of as emulating " ` x ` is not free in ` ph ` ."  With this convention,
       the meaning of "not free" is less restrictive than the usual textbook
       definition; for example ` x ` would not (for us) be free in ` x = x ` by
       ~ hbequid .  This theorem scheme can be proved as a metatheorem of
       Mendelson's axiom system, even though it is slightly stronger than his
       Axiom 5. $)
    stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wi wal 19.21 biimpi ) ABECFABCFEABCDGH $.
      $( [22-Sep-1993] $)
  $}

  ${
    19.21bi.1 $e |- ( ph -> A. x ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90. $)
    19.21bi $p |- ( ph -> ps ) $=
      ( wal ax-4 syl ) ABCEBDBCFG $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.21bbi.1 $e |- ( ph -> A. x A. y ps ) $.
    $( Inference removing double quantifier. $)
    19.21bbi $p |- ( ph -> ps ) $=
      ( wal 19.21bi ) ABDABDFCEGG $.
      $( [20-Apr-1994] $)
  $}

  ${
    19.27.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.27 of [Margaris] p. 90. $)
    19.27 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( wa wal 19.26 19.3 anbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.28.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.28 of [Margaris] p. 90. $)
    19.28 $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( wa wal 19.26 19.3 anbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.32.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.32 of [Margaris] p. 90. $)
    19.32 $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $=
      ( wn wi wal wo hbn 19.21 df-or albii 3bitr4i ) AEZBFZCGNBCGZFABHZCGAPHNBC
      ACDIJQOCABKLAPKM $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.31.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.31 of [Margaris] p. 90. $)
    19.31 $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $=
      ( wo wal 19.32 orcom albii 3bitr4i ) BAEZCFBACFZEABEZCFLBEBACDGMKCABHILBH
      J $.
      $( [5-Aug-1993] $)
  $}

  ${
    hbim1.1 $e |- ( ph -> A. x ph ) $.
    hbim1.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( A closed form of ~ hbim . $)
    hbim1 $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wi wal a2i 19.21 sylibr ) ABFZABCGZFKCGABLEHABCDIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    hbnd.1 $e |- ( ph -> A. x ph ) $.
    hbnd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbn . $)
    hbnd $p |- ( ph -> ( -. ps -> A. x -. ps ) ) $=
      ( wal wi wn alrimi hbnt syl ) ABBCFGZCFBHZMCFGALCDEIBCJK $.
      $( [3-Jan-2002] $)
  $}

  ${
    hbimd.1 $e |- ( ph -> A. x ph ) $.
    hbimd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbimd.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbim . $)
    hbimd $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi wal imim2d ax-4 imim1i ax-i5r syl syl6 imim1d alimd syld ) ABCHZBDIZ
      CHZDIZSDIASBCDIZHZUBACUCBGJUDTUCHUBTBUCBDKLBCDMNOAUASDEABTCFPQR $.
      $( [2-Feb-2015] $) $( [1-Jan-2002] $)
  $}

  ${
    hbbid.1 $e |- ( ph -> A. x ph ) $.
    hbbid.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbbid.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbbi . $)
    hbbid $p |- ( ph -> ( ( ps <-> ch ) -> A. x ( ps <-> ch ) ) ) $=
      ( wi wa wal wb hbimd anim12d dfbi2 albiim 3imtr4g ) ABCHZCBHZIQDJZRDJZIBC
      KZUADJAQSRTABCDEFGLACBDEGFLMBCNBCDOP $.
      $( [1-Jan-2002] $)
  $}

  $( Closed form of Theorem 19.21 of [Margaris] p. 90. $)
  19.21t $p |- ( A. x ( ph -> A. x ph ) ->
               ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wal wi alim imim2d com12 a4s hba1 ax-4 a1i hbimd imim2i alimi syl6 impbid
    ) AACDZEZCDZABEZCDZABCDZEZSUBUDECUBSUDUBRUCAABCFGHITUDUDCDUBTAUCCSCJSCKUCUC
    CDETBCJLMUDUACUCBABCKNOPQ $.
    $( [27-May-1997] $)

  ${
    aaan.1 $e |- ( ph -> A. y ph ) $.
    aaan.2 $e |- ( ps -> A. x ps ) $.
    $( Rearrange universal quantifiers. $)
    aaan $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) ) $=
      ( wa wal 19.28 albii hbal 19.27 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
      $( [12-Aug-1993] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    The existential quantifier
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If a wff is true, it is true for at least one instance.  Special case of
     Theorem 19.8 of [Margaris] p. 89. $)
  19.8a $p |- ( ph -> E. x ph ) $=
    ( wex wi wal id hbe1 19.23 mpbir a4i ) AABCZDZBLBEKKDKFAKBABGHIJ $.
    $( [5-Aug-1993] $)

  ${
    19.23bi.1 $e |- ( E. x ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90. $)
    19.23bi $p |- ( ph -> ps ) $=
      ( wex 19.8a syl ) AACEBACFDG $.
      $( [5-Aug-1993] $)
  $}

  ${
    exlimi.1 $e |- ( ps -> A. x ps ) $.
    exlimi.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (The proof was
       shortened by Andrew Salmon, 13-May-2011.) $)
    exlimi $p |- ( E. x ph -> ps ) $=
      ( wi wex 19.23 mpgbi ) ABFACGBFCABCDHEI $.
      $( [16-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    exlimd.1 $e |- ( ph -> A. x ph ) $.
    exlimd.2 $e |- ( ch -> A. x ch ) $.
    exlimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90. $)
    exlimd $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wi wal wex alrimi 19.23 sylib ) ABCHZDIBDJCHANDEGKBCDFLM $.
      $( [28-Jan-1997] $)
  $}

  $( Theorem 19.22 of [Margaris] p. 90.  (The proof was shortened by Wolf
     Lammen, 4-Jul-2014.) $)
  exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi wal wex hba1 hbe1 19.8a imim2i a4s exlimd ) ABDZCEABCFZCMCGBCHMANDCBNA
    BCIJKL $.
    $( [2-Feb-2015] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ exim as of 4-Jul-2014. $)
  eximOLD $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi wal wn wex con3 al2imi con3d df-ex 3imtr4g ) ABDZCEZAFZCEZFBFZCEZFACGB
    CGNRPMQOCABHIJACKBCKL $.
    $( [5-Aug-1993] $)

  ${
    eximi.1 $e |- ( ph -> ps ) $.
    $( Inference adding existential quantifier to antecedent and consequent. $)
    eximi $p |- ( E. x ph -> E. x ps ) $=
      ( wi wex exim mpg ) ABEACFBCFECABCGDH $.
      $( [5-Aug-1993] $)

    $( Inference adding 2 existential quantifiers to antecedent and
       consequent. $)
    2eximi $p |- ( E. x E. y ph -> E. x E. y ps ) $=
      ( wex eximi ) ADFBDFCABDEGG $.
      $( [3-Feb-2005] $)
  $}

  $( A transformation of quantifiers and logical connectives. $)
  alinexa $p |- ( A. x ( ph -> -. ps ) <-> -. E. x ( ph /\ ps ) ) $=
    ( wn wi wal wa wex imnan albii alnex bitri ) ABDEZCFABGZDZCFNCHDMOCABIJNCKL
    $.
    $( [19-Aug-1993] $)

  $( Theorem 19.18 of [Margaris] p. 90. $)
  exbi $p |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) ) $=
    ( wb wal wex wi bi1 alimi exim syl bi2 impbid ) ABDZCEZACFZBCFZOABGZCEPQGNR
    CABHIABCJKOBAGZCEQPGNSCABLIBACJKM $.
    $( [5-Aug-1993] $)

  ${
    exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding existential quantifier to both sides of an
       equivalence. $)
    exbii $p |- ( E. x ph <-> E. x ps ) $=
      ( wb wex exbi mpg ) ABEACFBCFECABCGDH $.
      $( [24-May-1994] $)

    $( Inference adding 2 existential quantifiers to both sides of an
       equivalence. $)
    2exbii $p |- ( E. x E. y ph <-> E. x E. y ps ) $=
      ( wex exbii ) ADFBDFCABDEGG $.
      $( [16-Mar-1995] $)

    $( Inference adding 3 existential quantifiers to both sides of an
       equivalence. $)
    3exbii $p |- ( E. x E. y E. z ph <-> E. x E. y E. z ps ) $=
      ( wex exbii 2exbii ) AEGBEGCDABEFHI $.
      $( [2-May-1995] $)
  $}

  $( Commutation of conjunction inside an existential quantifier. $)
  exancom $p |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) ) $=
    ( wa ancom exbii ) ABDBADCABEF $.
    $( [18-Aug-1993] $)

  ${
    eximd.1 $e |- ( ph -> A. x ph ) $.
    eximd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90. $)
    eximd $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( wi wal wex alrimi exim syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
      $( [20-May-1996] $)
  $}

  ${
    nex.1 $e |- -. ph $.
    $( Generalization rule for negated wff. $)
    nex $p |- -. E. x ph $=
      ( wn wex alnex mpgbi ) ADABEDBABFCG $.
      $( [18-May-1994] $)
  $}

  ${
    nexd.1 $e |- ( ph -> A. x ph ) $.
    nexd.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff. $)
    nexd $p |- ( ph -> -. E. x ps ) $=
      ( wn wal wex alrimi alnex sylib ) ABFZCGBCHFALCDEIBCJK $.
      $( [2-Jan-2002] $)
  $}

  ${
    exbid.1 $e |- ( ph -> A. x ph ) $.
    exbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction rule). $)
    exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( wb wal wex alrimi exbi syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
      $( [5-Aug-1993] $)
  $}

  $( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (The proof was shortened by Andrew
     Salmon, 29-Jun-2011.) $)
  exsimpl $p |- ( E. x ( ph /\ ps ) -> E. x ph ) $=
    ( wa simpl eximi ) ABDACABEF $.
    $( [29-Jun-2011] $) $( [25-Sep-2010] $)

  $( Theorem 19.29 of [Margaris] p. 90.  (The proof was shortened by Andrew
     Salmon, 13-May-2011.) $)
  19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa wi pm3.2 alimi exim syl imp ) ACDZBCEZABFZCEZMBOGZCDNPGAQCABHI
    BOCJKL $.
    $( [16-May-2011] $) $( [5-Aug-1993] $)

  $( Variation of Theorem 19.29 of [Margaris] p. 90. $)
  19.29r $p |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa 19.29 ancom exancom 3imtr4i ) BCDZACEZFBAFCELKFABFCEBACGLKHABC
    IJ $.
    $( [18-Aug-1993] $)

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with double
     quantification. $)
  19.29r2 $p |- ( ( E. x E. y ph /\ A. x A. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wex wal wa 19.29r eximi syl ) ADEZCEBDFZCFGKLGZCEABGDEZCEKLCHMNCABDHIJ $.
    $( [3-Feb-2005] $)

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with mixed
     quantification. $)
  19.29x $p |- ( ( E. x A. y ph /\ A. x E. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wal wex wa 19.29r 19.29 eximi syl ) ADEZCFBDFZCEGLMGZCFABGDFZCFLMCHNOCABD
    IJK $.
    $( [11-Feb-2005] $)

  $( Theorem 19.6 of [Margaris] p. 89. $)
  alex $p |- ( A. x ph <-> -. E. x -. ph ) $=
    ( wal wn wex notnot albii alnex bitri ) ABCADZDZBCJBEDAKBAFGJBHI $.
    $( [5-Aug-1993] $)

  $( Part of theorem *11.5 in [WhiteheadRussell] p. 164.  (Contributed by
     Andrew Salmon, 24-May-2011.) $)
  2nalexn $p |- ( -. A. x A. y ph <-> E. x E. y -. ph ) $=
    ( wn wex wal df-ex alex albii xchbinxr bicomi ) ADCEZBEZACFZBFZDMLDZBFOLBGN
    PBACHIJK $.
    $( [24-May-2011] $)

  $( Theorem 19.14 of [Margaris] p. 90. $)
  exnal $p |- ( E. x -. ph <-> -. A. x ph ) $=
    ( wal wn wex alex con2bii ) ABCADBEABFG $.
    $( [5-Aug-1993] $)

  $( A relationship between two quantifiers and negation. $)
  alexn $p |- ( A. x E. y -. ph <-> -. E. x A. y ph ) $=
    ( wn wex wal exnal albii alnex bitri ) ADCEZBFACFZDZBFLBEDKMBACGHLBIJ $.
    $( [18-Aug-1993] $)

  $( Theorem *11.51 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.)  (The proof was shortened by Wolf Lammen,
     25-Sep-2014.) $)
  2exnexn $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $=
    ( wn wex wal alexn con2bii ) ADCEBFACFBEABCGH $.
    $( [25-Sep-2014] $) $( [24-May-2011] $)

  $( Obsolete proof of ~ 2exnexn as of 25-Sep-2014. $)
  2exnexnOLD $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $=
    ( wal wex wn df-ex exnal albii notbii bitr4i ) ACDZBELFZBDZFAFCEZBDZFLBGPNO
    MBACHIJK $.
    $( [24-May-2011] $)

  $( A transformation of quantifiers and logical connectives.  (The proof was
     shortened by Wolf Lammen, 4-Sep-2014.) $)
  exanali $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $=
    ( wn wa wex wi wal annim exbii exnal bitri ) ABDEZCFABGZDZCFNCHDMOCABIJNCKL
    $.
    $( [4-Sep-2014] $) $( [25-Mar-1996] $)

  $( Obsolete proof of ~ exanali as of 4-Sep-2014. $)
  exanaliOLD $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $=
    ( wi wal wn wa wex iman albii alnex bitri con2bii ) ABDZCEZABFGZCHZOPFZCEQF
    NRCABIJPCKLM $.
    $( [25-Mar-1996] $)

  $( Forward direction of Theorem 19.35 of [Margaris] p. 90.
     (Contributed by Mario Carneiro, 2-Feb-2015.) $)
  19.35-1 $p |- ( E. x ( ph -> ps ) -> ( A. x ph -> E. x ps ) ) $=
    ( wal wi wex wa 19.29 pm3.35 eximi syl expcom ) ACDZABEZCFZBCFZMOGANGZCFPAN
    CHQBCABIJKL $.
    $( [2-Feb-2015] $)

  $( Theorem 19.35 of [Margaris] p. 90.  This theorem is useful for moving an
     implication (in the form of the right-hand side) into the scope of a
     single existential quantifier.  (The proof was shortened by Wolf Lammen,
     27-Jun-2014.) $)
  19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
    ( wi wex wal wn wa 19.26 annim albii alnex anbi2i 3bitr3i con4bii ) ABDZCEZ
    ACFZBCEZDZPGZCFZRSGZHZQGTGABGZHZCFRUECFZHUBUDAUECIUFUACABJKUGUCRBCLMNPCLRSJ
    NO $.
    $( [27-Jun-2014] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ 19.35 as of 27-Jun-2014. $)
  19.35OLD $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
    ( wal wn wi wex wa 19.26 annim albii df-an 3bitr3i con2bii imbi2i 3bitr4ri
    df-ex ) ACDZBEZCDZEZFZABFZEZCDZERBCGZFUCCGUEUBASHZCDRTHUEUBEASCIUGUDCABJKRT
    LMNUFUARBCQOUCCQP $.
    $( [5-Aug-1993] $)

  ${
    19.35i.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.35 of [Margaris] p. 90. $)
    19.35i $p |- ( A. x ph -> E. x ps ) $=
      ( wi wex wal 19.35-1 ax-mp ) ABECFACGBCFEDABCHI $.
      $( [2-Feb-2015] $) $( [5-Aug-1993] $)
  $}

  ${
    19.35ri.1 $e |- ( A. x ph -> E. x ps ) $.
    $( Inference from Theorem 19.35 of [Margaris] p. 90. $)
    19.35ri $p |- E. x ( ph -> ps ) $=
      ( wi wex wal 19.35 mpbir ) ABECFACGBCFEDABCHI $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem 19.25 of [Margaris] p. 90. $)
  19.25 $p |- ( A. y E. x ( ph -> ps ) ->
              ( E. y A. x ph -> E. y E. x ps ) ) $=
    ( wi wex wal 19.35-1 alimi exim syl ) ABECFZDGACGZBCFZEZDGMDFNDFELODABCHIMN
    DJK $.
    $( [2-Feb-2015] $) $( [5-Aug-1993] $)

  $( Theorem 19.30 of [Margaris] p. 90.  (The proof was shortened by Andrew
     Salmon, 25-May-2011.) $)
  19.30 $p |- ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) ) $=
    ( wn wi wal wex wo exnal exim syl5bir df-or albii 3imtr4i ) ADZBEZCFZACFZDZ
    BCGZEABHZCFRTHSOCGQTACIOBCJKUAPCABLMRTLN $.
    $( [25-May-2011] $) $( [5-Aug-1993] $)

  $( Theorem 19.43 of [Margaris] p. 90.
     (The proof was shortened by Mario Carneiro, 2-Feb-2015.) $)
  19.43 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wex hbe1 hbor 19.8a orim12i exlimi orc eximi olc jaoi impbii ) ABDZCEZ
    ACEZBCEZDZPTCRSCACFBCFGARBSACHBCHIJRQSAPCABKLBPCBAMLNO $.
    $( [2-Feb-2015] $) $( [5-Aug-1993] $)

  $( Obsolete proof of ~ 19.43 as of 27-Jun-2014. $)
  19.43OLD $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wn wal wex wa ioran albii 19.26 alnex anbi12i 3bitri notbii df-ex oran
    3bitr4i ) ABDZEZCFZEACGZEZBCGZEZHZESCGUBUDDUAUFUAAEZBEZHZCFUGCFZUHCFZHUFTUI
    CABIJUGUHCKUJUCUKUEACLBCLMNOSCPUBUDQR $.
    $( [5-Aug-1993] $)

  $( The antecedent provides a condition implying the converse of ~ 19.33 .
     Compare Theorem 19.33 of [Margaris] p. 90.  This variation of ~ 19.33b
     is intuitionistically valid with a slight modification of the antecedent.
     (Contributed by Mario Carneiro, 2-Feb-2015.) $)
  19.33b2 $p |- ( ( -. E. x ph \/ -. E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    ( wex wn wal orcom alnex orbi12i bitr4i pm2.53 orcoms al2imi orim12d syl5bi
    wo wi com12 19.33 impbid1 ) ACDEZBCDEZPZABPZCFZACFZBCFZPZUEUCUHUCBEZCFZAEZC
    FZPZUEUHUCUBUAPUMUAUBGUJUBULUABCHACHIJUEUJUFULUGUDUIACBAUIAQBAKLMUDUKBCABKM
    NORABCST $.
    $( [2-Feb-2015] $)

  $( The antecedent provides a condition implying the converse of ~ 19.33 .
     Compare Theorem 19.33 of [Margaris] p. 90.  (The proof was shortened by Wolf Lammen,
     5-Jul-2014.)
     (The proof was shortened by Mario Carneiro, 2-Feb-2015.) $)
  19.33b $p |- ( -. ( E. x ph /\ E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    ( wex wa wn wo wal wb ianor 19.33b2 sylbi ) ACDZBCDZEFMFNFGABGCHACHBCHGIMNJ
    ABCKL $.
    $( [2-Feb-2015] $) $( [27-Mar-2004] $)

  $( Obsolete proof of ~ 19.33b as of 22-Mar-2014. $)
  19.33bOLD $p |- ( -. ( E. x ph /\ E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    ( wex wa wn wo wal wi ianor alnex wb biorf alimi albi syl olc syl6bir 19.30
    sylbir orc a1i pm2.21 jaod syl5 jaoi sylbi 19.33 impbid1 ) ACDZBCDZEFZABGZC
    HZACHZBCHZGZULUJFZUKFZGUNUQIZUJUKJURUTUSURAFZCHZUTACKVBUNUPUQVBBUMLZCHUPUNL
    VAVCCABMNBUMCOPUPUOQRTUNUOUKGUSUQABCSUSUOUQUKUOUQIUSUOUPUAUBUKUQUCUDUEUFUGA
    BCUHUI $.
    $( [25-May-2011] $) $( [27-Mar-2004] $)

  $( Theorem 19.40 of [Margaris] p. 90. $)
  19.40 $p |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) ) $=
    ( wa wex exsimpl simpr eximi jca ) ABDZCEACEBCEABCFJBCABGHI $.
    $( [5-Aug-1993] $)

  $( Theorem *11.42 in [WhiteheadRussell] p. 163.  Theorem 19.40 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  19.40-2 $p |- ( E. x E. y ( ph /\ ps ) ->
        ( E. x E. y ph /\ E. x E. y ps ) ) $=
    ( wa wex 19.40 eximi syl ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.
    $( [24-May-2011] $)

  $( Add/remove a conjunct in the scope of an existential quantifier.
     (Contributed by Raph Levien, 3-Jul-2006.) $)
  exintrbi $p |- ( A. x ( ph -> ps ) -> ( E. x ph <-> E. x ( ph /\ ps ) ) ) $=
    ( wi wal wa wb wex pm4.71 albii exbi sylbi ) ABDZCEAABFZGZCEACHNCHGMOCABIJA
    NCKL $.
    $( [3-Jul-2006] $)

  $( Introduce a conjunct in the scope of an existential quantifier. $)
  exintr $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) ) $=
    ( wi wal wex wa exintrbi biimpd ) ABDCEACFABGCFABCHI $.
    $( [11-Aug-1993] $)

  $( Lemma used in proofs of substitution properties. $)
  equs3 $p |- ( E. x ( x = y /\ ph ) <-> -. A. x ( x = y -> -. ph ) ) $=
    ( weq wn wi wal wa wex alinexa con2bii ) BCDZAEFBGLAHBILABJK $.
    $( [5-Aug-1993] $)

  $( Abbreviated version of ~ ax-6o . $)
  a6e $p |- ( E. x A. x ph -> ph ) $=
    ( wal wex hba1 id exlimi ax-4 syl ) ABCZBDJAJJBABEJFGABHI $.
    $( [5-Aug-1993] $)

  ${
    hbex.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` . $)
    hbex $p |- ( E. y ph -> A. x E. y ph ) $=
      ( wex wal hbe1 hbal 19.8a alrimi exlimi ) AACEZBFCLCBACGHALBDACIJK $.
      $( [2-Feb-2015] $) $( [5-Aug-1993] $)
  $}

  $( Theorem 19.2 of [Margaris] p. 89, generalized to use two set variables.
     (Contributed by O'Cat, 31-Mar-2008.) $)
  19.2 $p |- ( A. x ph -> E. y ph ) $=
    ( wex 19.8a a4s ) AACDBACEF $.
    $( [31-Mar-2008] $)

  $( A closed version of one direction of ~ 19.9 . $)
  19.9t $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $=
    ( wal wi wex id ax-gen 19.23t mpbii ) AABCDBCAADZBCABEADJBAFGAABHI $.
    $( [5-Aug-1993] $)

  ${
    19.9.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.) $)
    19.9 $p |- ( E. x ph <-> ph ) $=
      ( wex wal wi 19.9t mpg 19.8a impbii ) ABDZAAABEFKAFBABGCHABIJ $.
      $( [24-Mar-2007] $)
  $}

  ${
    19.9d.1 $e |- ( ps -> A. x ps ) $.
    19.9d.2 $e |- ( ps -> ( ph -> A. x ph ) ) $.
    $( A deduction version of one direction of ~ 19.9 . $)
    19.9d $p |- ( ps -> ( E. x ph -> ph ) ) $=
      ( wal wi wex alimi 19.9t 3syl ) BBCFAACFGZCFACHAGDBLCEIACJK $.
      $( [5-Aug-1993] $)
  $}

  $( One direction of Theorem 19.11 of [Margaris] p. 89. $)
  excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $=
    ( wex 19.8a 2eximi hbe1 hbex 19.9 sylib ) ACDBDABDZCDZBDLAKBCABEFLBKBCABGHI
    J $.
    $( [5-Aug-1993] $)

  $( Theorem 19.11 of [Margaris] p. 89. $)
  excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $=
    ( wex excomim impbii ) ACDBDABDCDABCEACBEF $.
    $( [5-Aug-1993] $)

  $( Theorem 19.12 of [Margaris] p. 89.  Assuming the converse is a mistake
     sometimes made by beginners!  But sometimes the converse does hold, as in
     ~ 19.12vv . $)
  19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $=
    ( wal wex hba1 hbex ax-4 eximi alrimi ) ACDZBEABECKCBACFGKABACHIJ $.
    $( [5-Aug-1993] $)

  ${
    19.19.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.19 of [Margaris] p. 90. $)
    19.19 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) ) $=
      ( wex wb wal 19.9 exbi syl5bbr ) AACEABFCGBCEACDHABCIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.36.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.36 of [Margaris] p. 90. $)
    19.36 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( wi wex wal 19.35 19.9 imbi2i bitri ) ABECFACGZBCFZELBEABCHMBLBCDIJK $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.36i.1 $e |- ( ps -> A. x ps ) $.
    19.36i.2 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.36 of [Margaris] p. 90. $)
    19.36i $p |- ( A. x ph -> ps ) $=
      ( wal wex 19.35i id exlimi syl ) ACFBCGBABCEHBBCDBIJK $.
      $( [2-Feb-2015] $) $( [5-Aug-1993] $)
  $}

  ${
    19.37.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.37 of [Margaris] p. 90. $)
    19.37 $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( wi wex wal 19.35 19.3 imbi1i bitri ) ABECFACGZBCFZEAMEABCHLAMACDIJK $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem 19.38 of [Margaris] p. 90. $)
  19.38 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $=
    ( wex wal wi hbe1 hba1 hbim 19.8a ax-4 imim12i alrimi ) ACDZBCEZFABFCNOCACG
    BCHIANOBACJBCKLM $.
    $( [5-Aug-1993] $)

  $( Theorem 19.39 of [Margaris] p. 90. $)
  19.39 $p |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wex wi wal 19.2 imim1i 19.35 sylibr ) ACDZBCDZEACFZLEABECDMKLACCGHABCIJ
    $.
    $( [5-Aug-1993] $)

  $( Theorem 19.24 of [Margaris] p. 90. $)
  19.24 $p |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wal wi wex 19.2 imim2i 19.35 sylibr ) ACDZBCDZEKBCFZEABECFLMKBCCGHABCIJ
    $.
    $( [5-Aug-1993] $)

  ${
    19.44.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.44 of [Margaris] p. 90. $)
    19.44 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $=
      ( wo wex 19.43 19.9 orbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    19.45.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.45 of [Margaris] p. 90. $)
    19.45 $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $=
      ( wo wex 19.43 19.9 orbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
      $( [5-Aug-1993] $)
  $}

  $( Theorem 19.34 of [Margaris] p. 90. $)
  19.34 $p |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) ) $=
    ( wal wex wo 19.2 orim1i 19.43 sylibr ) ACDZBCEZFACEZLFABFCEKMLACCGHABCIJ
    $.
    $( [5-Aug-1993] $)

  ${
    19.41.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.41 of [Margaris] p. 90.  (The proof was shortened by Andrew
       Salmon, 25-May-2011.) $)
    19.41 $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 id exlimi anim2i syl pm3.21 eximd impcom impbii ) ABEZCFZA
      CFZBEZQRBCFZESABCGTBRBBCDBHIJKBRQBAPCDBALMNO $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    19.42.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.42 of [Margaris] p. 90. $)
    19.42 $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( wa wex 19.41 exancom ancom 3bitr4i ) BAECFBCFZAEABECFAKEBACDGABCHAKIJ
      $.
      $( [18-Aug-1993] $)
  $}

  $( Swap 1st and 3rd existential quantifiers. $)
  excom13 $p |- ( E. x E. y E. z ph <-> E. z E. y E. x ph ) $=
    ( wex excom exbii 3bitri ) ADEZCEBEIBEZCEABEZDEZCEKCEDEIBCFJLCABDFGKCDFH $.
    $( [9-Mar-1995] $)

  $( Rotate existential quantifiers. $)
  exrot3 $p |- ( E. x E. y E. z ph <-> E. y E. z E. x ph ) $=
    ( wex excom13 excom bitri ) ADECEBEABEZCEDEIDECEABCDFIDCGH $.
    $( [17-Mar-1995] $)

  $( Rotate existential quantifiers twice. $)
  exrot4 $p |- ( E. x E. y E. z E. w ph <-> E. z E. w E. x E. y ph ) $=
    ( wex excom13 exbii bitri ) AEFDFCFZBFACFZDFEFZBFKBFEFDFJLBACDEGHKBEDGI $.
    $( [9-Mar-1995] $)

  ${
    nexr.1 $e |- -. E. x ph $.
    $( Inference from ~ 19.8a .  (Contributed by Jeff Hankins, 26-Jul-2009.) $)
    nexr $p |- -. ph $=
      ( wex 19.8a mto ) AABDCABEF $.
      $( [26-Jul-2009] $)
  $}

  ${
    exan.1 $e |- ( E. x ph /\ ps ) $.
    $( Place a conjunct in the scope of an existential quantifier.  (The proof
       was shortened by Andrew Salmon, 25-May-2011.) $)
    exan $p |- E. x ( ph /\ ps ) $=
      ( wex wal wa hbe1 19.28 mpgbi 19.29r ax-mp ) ACEZBCFGZABGCEMBGNCMBCACHIDJ
      ABCKL $.
      $( [25-May-2011] $) $( [18-Aug-1993] $)
  $}

  ${
    hbexd.1 $e |- ( ph -> A. y ph ) $.
    hbexd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbex . $)
    hbexd $p |- ( ph -> ( E. y ps -> A. x E. y ps ) ) $=
      ( wex wal eximd 19.12 syl6 ) ABDGZBCHZDGLCHABMDEFIBDCJK $.
      $( [2-Jan-2002] $)
  $}

  ${
    eeor.1 $e |- ( ph -> A. y ph ) $.
    eeor.2 $e |- ( ps -> A. x ps ) $.
    $( Rearrange existential quantifiers. $)
    eeor $p |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) ) $=
      ( wo wex 19.45 exbii hbex 19.44 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
      $( [8-Aug-1994] $)
  $}

  $( Quantified "excluded middle."  Exercise 9.2a of Boolos, p. 111,
     _Computability and Logic_. $)
  qexmid $p |- E. x ( ph -> A. x ph ) $=
    ( wal 19.8a 19.35ri ) AABCZBFBDE $.
    $( [10-Dec-2000] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Equality theorems without distinct variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( At least one individual exists.  This is not a theorem of free logic,
     which is sound in empty domains.  For such a logic, we would add this
     theorem as an axiom of set theory (Axiom 0 of [Kunen] p. 10).  In the
     system consisting of ~ ax-5 through ~ ax-14 and ~ ax-17 , all axioms other
     than ~ ax-9 are believed to be theorems of free logic, although the system
     without ~ ax-9 is probably not complete in free logic. $)
  a9e $p |- E. x x = y $=
    ( ax-i9 ) ABC $.
    $( [3-Feb-2015] $) $( [5-Aug-1993] $)

  $( Show that the original axiom ~ ax-9o can be derived from ~ ax-9 and
     others.  See ~ ax9 for the rederivation of ~ ax-9 from ~ ax-9o .

     Normally, ~ ax9o should be used rather than ~ ax-9o , except by theorems
     specifically studying the latter's properties. $)
  ax9o $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
    ( cv wceq wex wal wi a9e wa 19.29r hba1 pm3.35 exlimi ax-4 syl mpan ) BDCDE
    ZBFZRABGZHZBGZABCISUBJRUAJZBFZARUABKUDTAUCTBABLRTMNABOPPQ $.
    $( [3-Feb-2015] $) $( [5-Aug-1993] $)

  $( A variant of ~ ax-9 .  Axiom scheme C10' in [Megill] p. 448 (p. 16 of the
     preprint).

     This axiom is redundant, as shown by theorem ~ ax9o .

     Normally, ~ ax9o should be used rather than ~ ax-9o , except by theorems
     specifically studying the latter's properties. $)
  ax-9o $a |- ( A. x ( x = y -> A. x ph ) -> ph ) $.

  $( Rederivation of axiom ~ ax-9 from the orginal version, ~ ax-9o .  See
     ~ ax9o for the derivation of ~ ax-9o from ~ ax-9 .  Lemma L18 in [Megill]
     p. 446 (p. 14 of the preprint).

     This theorem should not be referenced in any proof.  Instead, use ~ ax-9
     above so that uses of ~ ax-9 can be more easily identified. $)
  ax9 $p |- -. A. x -. x = y $=
    ( weq wn wal wi ax-9o modal-b mpg ) ABCZJDAEDZAEFKAKABGJAHI $.
    $( [5-Aug-1993] $)

  $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.
     Alternate proof of ~ equid from older axioms ~ ax-6o and ~ ax-9o . $)
  equidALT $p |- x = x $=
    ( weq wal wn wi ax-12 pm2.43i alimi ax-9o syl ax-6o pm2.61i ) AABZACZDZACZM
    PMNEZACMOQAOQAAAFGHMAAIJMAKL $.
    $( [5-Aug-1993] $)

  ${
    $d x y $.
    $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.
       This proof is similar to Tarski's and makes use of a dummy variable
       ` y ` .  See ~ equid for a proof that avoids dummy variables (but is
       less intuitive). $)
    equid1 $p |- x = x $=
      ( vy weq wex a9e ax-17 ax-8 pm2.43i exlimi ax-mp ) BACZBDAACZBAEKLBLBFKLB
      AAGHIJ $.
      $( [1-Apr-2005] $)
  $}

  $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.  This
     is often an axiom of equality in textbook systems, but we don't need it as
     an axiom since it can be proved from our other axioms. (The proof has been
     modified to use ~ equid1 for compatibility with intuitionistic logic.) $)
  equid $p |- x = x $=
    ( equid1 ) AB $.
    $( [3-Feb-2015] $) $( [30-Nov-2008] $)

  $( One of the two equality axioms of standard predicate calculus, called
     reflexivity of equality.  (The other one is ~ stdpc7 .)  Axiom 6 of
     [Mendelson] p. 95.  Mendelson doesn't say why he prepended the redundant
     quantifier, but it was probably to be compatible with free logic (which is
     valid in the empty domain). $)
  stdpc6 $p |- A. x x = x $=
    ( weq equid ax-gen ) AABAACD $.
    $( [16-Feb-2005] $)

  $( Commutative law for equality.  Lemma 7 of [Tarski] p. 69. $)
  equcomi $p |- ( x = y -> y = x ) $=
    ( weq equid1 ax-8 mpi ) ABCAACBACADABAEF $.
    $( [5-Aug-1993] $)

  $( Commutative law for equality. $)
  equcom $p |- ( x = y <-> y = x ) $=
    ( weq equcomi impbii ) ABCBACABDBADE $.
    $( [20-Aug-1993] $)

  ${
    equcoms.1 $e |- ( x = y -> ph ) $.
    $( An inference commuting equality in antecedent.  Used to eliminate the
       need for a syllogism. $)
    equcoms $p |- ( y = x -> ph ) $=
      ( weq equcomi syl ) CBEBCEACBFDG $.
      $( [5-Aug-1993] $)
  $}

  $( A transitive law for equality. $)
  equtr $p |- ( x = y -> ( y = z -> x = z ) ) $=
    ( weq wi ax-8 equcoms ) BCDACDEBABACFG $.
    $( [23-Aug-1993] $)

  $( A transitive law for equality.  Lemma L17 in [Megill] p. 446 (p. 14 of the
     preprint). $)
  equtrr $p |- ( x = y -> ( z = x -> z = y ) ) $=
    ( weq equtr com12 ) CADABDCBDCABEF $.
    $( [23-Aug-1993] $)

  $( A transitive law for equality.  (The proof was shortened by Andrew Salmon,
     25-May-2011.) $)
  equtr2 $p |- ( ( x = z /\ y = z ) -> x = y ) $=
    ( weq wi equtrr equcoms impcom ) BCDACDZABDZIJECBCBAFGH $.
    $( [25-May-2011] $) $( [12-Aug-1993] $)

  $( An equivalence law for equality. $)
  equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $=
    ( weq ax-8 equtr impbid ) ABDACDBCDABCEABCFG $.
    $( [5-Aug-1993] $)

  $( An equivalence law for equality. $)
  equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
    ( weq equtrr wi equcoms impbid ) ABDCADZCBDZABCEJIFBABACEGH $.
    $( [5-Aug-1993] $)

  $( An identity law for the non-logical predicate. $)
  elequ1 $p |- ( x = y -> ( x e. z <-> y e. z ) ) $=
    ( weq wel ax-13 wi equcoms impbid ) ABDACEZBCEZABCFKJGBABACFHI $.
    $( [5-Aug-1993] $)

  $( An identity law for the non-logical predicate. $)
  elequ2 $p |- ( x = y -> ( z e. x <-> z e. y ) ) $=
    ( weq wel ax-14 wi equcoms impbid ) ABDCAEZCBEZABCFKJGBABACFHI $.
    $( [5-Aug-1993] $)

  ${
    ax11i.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax11i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference that has ~ ax-11 (without ` A. y ` ) as its conclusion and
       doesn't require ~ ax-10 , ~ ax-11 , or ~ ax-12 for its proof.  The
       hypotheses may be eliminable without one or more of these axioms in
       special cases.  Proof similar to Lemma 16 of [Tarski] p. 70. $)
    ax11i $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wi wal biimprcd alrimi syl6bi ) CDGZABMAHZCIEBNCFMABEJKL $.
      $( [20-May-2008] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Axioms ax-10 and ax-11
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Show that ~ ax-10o can be derived from ~ ax-10 .  An open problem is
     whether this theorem can be derived from ~ ax-10 and the others when
     ~ ax-11 is replaced with ~ ax-11o .  See theorem ~ ax10 for the
     rederivation of ~ ax-10 from ~ ax10o .

     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties. $)
  ax10o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax-10 ax-11 equcoms a4s pm2.27 al2imi sylsyld ) BCDZBECBDZCEAB
    EZOAFZCEZACEBCGNPRFZBSCBACBHIJOQACOAKLM $.
    $( [16-May-2008] $)

  $( Axiom ~ ax-10o ("o" for "old") was the original version of ~ ax-10 ,
     before it was discovered (in May 2008) that the shorter ~ ax-10 could
     replace it.  It appears as Axiom scheme C11' in [Megill] p. 448 (p. 16 of
     the preprint).

     This axiom is redundant, as shown by theorem ~ ax10o .

     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties. $)
  ax-10o $a |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $.

  $( Rederivation of ~ ax-10 from original version ~ ax-10o .  See theorem
     ~ ax10o for the derivation of ~ ax-10o from ~ ax-10 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-10
     above so that uses of ~ ax-10 can be more easily identified. $)
  ax10 $p |- ( A. x x = y -> A. y y = x ) $=
    ( weq wal ax-10o pm2.43i equcomi alimi syl ) ABCZADZJBDZBACZBDKLJABEFJMBABG
    HI $.
    $( [16-May-2008] $)

  $( All variables are effectively bound in an identical variable specifier. $)
  hbae $p |- ( A. x x = y -> A. z A. x x = y ) $=
    ( cv wceq wal wi ax12or ax10o alequcoms pm2.43i syl5 ax-4 imim1i jaoi ax-mp
    wo a4s a5i ax-7 syl ) ADZBDZEZAFZUDCFZAFUECFUDUFACDZUBECFZUGUCECFZUDUFGZCFZ
    QZQUEUFGZABCHUHUMULUMACUDACIJUIUMUKUMBCUEUDBFZUCUGEBFUFUEUNUDABIKUDBCILJUJU
    MCUEUDUFUDAMNROOPSUDACTUA $.
    $( [3-Feb-2015] $) $( [5-Aug-1993] $)

  ${
    hbalequs.1 $e |- ( A. z A. x x = y -> ph ) $.
    $( Rule that applies ~ hbae to antecedent. $)
    hbaes $p |- ( A. x x = y -> ph ) $=
      ( weq wal hbae syl ) BCFBGZJDGABCDHEI $.
      $( [5-Aug-1993] $)
  $}

  $( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint). $)
  hbnae $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
    ( weq wal hbae hbn ) ABDAECABCFG $.
    $( [5-Aug-1993] $)

  ${
    hbnalequs.1 $e |- ( A. z -. A. x x = y -> ph ) $.
    $( Rule that applies ~ hbnae to antecedent. $)
    hbnaes $p |- ( -. A. x x = y -> ph ) $=
      ( weq wal wn hbnae syl ) BCFBGHZKDGABCDIEJ $.
      $( [5-Aug-1993] $)
  $}

  $( Lemma used in proofs of substitution properties.  (The proof was shortened
     by Mario Carneiro, 20-May-2014.) $)
  equs4 $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
    ( cv wceq wi wal wa wex a9e 19.29 mpan2 ancl imp eximi syl ) BDCDEZAFZBGZRQ
    HZBIZQAHZBISQBIUABCJRQBKLTUBBRQUBQAMNOP $.
    $( [20-May-2014] $) $( [5-Aug-1993] $)

  ${
    equsal.1 $e |- ( ps -> A. x ps ) $.
    equsal.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (The proof was shortened
       by Andrew Salmon, 12-Aug-2011.) $)
    equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal 19.3 syl6bbr pm5.74i albii a1d alrimi ax9o impbii bitr4i ) C
      DGZAHZCISBCIZHZCIZBTUBCSAUASABUAFBCEJKLMBUCBUBCEBUASENOBCDPQR $.
      $( [12-Aug-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    equsex.1 $e |- ( ps -> A. x ps ) $.
    equsex.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution. $)
    equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( cv wceq wa wex biimpa exlimi a9e idd biimprcd jcad eximd mpi impbii ) C
      GDGHZAIZCJZBUABCETABFKLBTCJUBCDMBTUACEBTTABTNTABFOPQRS $.
      $( [3-Feb-2015] $) $( [5-Aug-1993] $)
  $}

  ${
    dvelimfALT.1 $e |- ( ph -> A. x ph ) $.
    dvelimfALT.2 $e |- ( ps -> A. z ps ) $.
    dvelimfALT.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Proof of ~ dvelimf that uses ~ ax-10o (in the form of ~ ax10o ) but not
       ~ ax-11o , ~ ax-10 , or ~ ax-11 (if we replace uses of ~ ax10o by
       ~ ax-10o in the proofs of referenced theorems).  See ~ dvelimALT for a
       proof (of the distinct variable version ~ dvelim ) that doesn't require
       ~ ax-10 .  It is not clear whether a proof is possible that uses ~ ax-10
       but avoids ~ ax-11 , ~ ax-11o , and ~ ax-10o . $)
    dvelimfALT $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi hba1 ax10o alequcoms syl5 a1d wa hbnae hban ax-12 imp a1i
      hbimd hbald ex pm2.61i equsal albii 3imtr3g ) CDICJKZEDIZALZEJZUNCJZBBCJC
      EICJZUKUNUOLZLUPUQUKUNUNEJZUPUOUMEMURUOLECUNECNOPQUPKZUKUQUSUKRZUMCEUSUKE
      CEESCDESTUTULACUSUKCCECSCDCSTUSUKULULCJLEDCUAUBAACJLUTFUCUDUEUFUGABEDGHUH
      ZUNBCVAUIUJ $.
      $( [12-Nov-2002] $)
  $}

  ${
    dral1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
    dral1 $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal hbae biimpd alimd ax10o syld biimprd wi alequcoms impbid ) CDFC
      GZACGZBDGZQRBCGSQABCCDCHQABEIJBCDKLQSADGZRQBADCDDHQABEMJTRNDCADCKOLP $.
      $( [24-Nov-1994] $)
  $}

  ${
    dral2.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
    dral2 $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      ( weq wal hbae albid ) CDGCHABECDEIFJ $.
      $( [27-Feb-2005] $)
  $}

  ${
    drex1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
    drex1 $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $=
      ( cv wceq wal wex wa wi ax-i11e a4s alequcoms hbae biantrurd bitr3d exbid
      equcomi sylibd ax-4 bitr2d impbid ) CFZDFZGZCHZACIZBDIZUGUHUEUDGZAJZDIZUI
      UHULKZDCUJUMDADCLMNUGUKBDCDDOUGAUKBUGUJAUFUJCCDSMPEQRTUGUIUFBJZCIZUHUFUIU
      OKCBCDLMUGUNACCDCOUGABUNEUGUFBUFCUAPUBRTUC $.
      $( [3-Feb-2015] $) $( [27-Feb-2005] $)
  $}

  ${
    drex2.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
    drex2 $p |- ( A. x x = y -> ( E. z ph <-> E. z ps ) ) $=
      ( weq wal hbae exbid ) CDGCHABECDEIFJ $.
      $( [27-Feb-2005] $)
  $}

  ${
    exdistrf.1 $e |- ( -. A. x x = y -> ( ph -> A. y ph ) ) $.
    $( Distribution of existential quantifiers, with a bound-variable
       hypothesis saying that ` y ` is not free in ` ph ` , but ` x ` can be
       free in ` ph ` (and there is no distinct variable condition on ` x ` and
       ` y ` ).  (Contributed by Mario Carneiro, 20-Mar-2013.) $)
    exdistrf $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $=
      ( weq wal wa wex wi biidd drex1 drex2 hbe1 19.8a anim2i eximi sylbi hbnae
      19.9 syl6bir wn 19.40 19.9d anim1d syl5 eximd pm2.61i ) CDFCGZABHZDIZCIZA
      BDIZHZCIZJUIULUJCIZCIZUOUPUKCDCUJUJCDUIUJKLMUQUPUOUPCUJCNTUJUNCBUMABDOPQR
      UAUIUBZUKUNCCDCSUKADIZUMHURUNABDUCURUSAUMAURDCDDSEUDUEUFUGUH $.
      $( [20-Mar-2013] $)
  $}

  $( Closed theorem form of ~ a4im . $)
  a4imt $p |- ( A. x ( ( ps -> A. x ps ) /\ ( x = y -> ( ph -> ps ) ) ) ->
              ( A. x ph -> ps ) ) $=
    ( wal wi weq wa imim2 imim2d imp com23 al2imi ax9o syl6 ) BBCEZFZCDGZABFZFZ
    HZCEACERPFZCEBUAAUBCUARAPQTRAPFZFQSUCRBPAIJKLMBCDNO $.
    $( [15-Jan-2008] $)

  ${
    a4im.1 $e |- ( ps -> A. x ps ) $.
    a4im.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitition.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ a4im series of theorems requires that only one
       direction of the substitution hypothesis hold. $)
    a4im $p |- ( A. x ph -> ps ) $=
      ( wal weq wi syl6com alimi ax9o syl ) ACGCDHZBCGZIZCGBAPCNABOFEJKBCDLM $.
      $( [8-May-2008] $) $( [5-Aug-1993] $)
  $}

  ${
    a4ime.1 $e |- ( ph -> A. x ph ) $.
    a4ime.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitition.  Compare Lemma 14
       of [Tarski] p. 70. $)
    a4ime $p |- ( ph -> E. x ps ) $=
      ( cv wceq wex a9e com12 eximd mpi ) ACGDGHZCIBCICDJANBCENABFKLM $.
      $( [3-Feb-2015] $) $( [7-Aug-1994] $)
  $}

  ${
    a4imed.1 $e |- ( ch -> A. x ch ) $.
    a4imed.2 $e |- ( ch -> ( ph -> A. x ph ) ) $.
    a4imed.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Deduction version of ~ a4ime . $)
    a4imed $p |- ( ch -> ( ph -> E. x ps ) ) $=
      ( wex wa wal adantr imp 19.26 sylanbrc weq adantld a4ime ex ) CABDICAJZBD
      ETCDKZADKZTDKCUAAFLCAUBGMCADNODEPABCHQRS $.
      $( [5-Aug-1993] $)
  $}

  ${
    cbv1.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv1.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv1.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbv1 $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal wi a4s al2imi ax-7 syl6 weq com23 syl6d ax9o a7s syld ) AEIZDIZBDIZ
      UCEIZCEIZUBUCBEIZDIUDUABUFDABUFJEFKLBDEMNAUDUEJEDADIZUCCEUGUCDEOZCDIZJZDI
      CABUJDABUHCUIAUHBCHPGQLCDERNLST $.
      $( [5-Aug-1993] $)
  $}


  ${
    cbv2.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv2.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv2.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbv2 $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi bi1 syl6 cbv1 equcomi bi2 syl56 a7s impbid ) AEIDIBDIZCEI
      ZABCDEFGADEJZBCKZBCLHBCMNOAUBUALEDACBEDGFEDJUCAUDCBLEDPHBCQROST $.
      $( [5-Aug-1993] $)
  $}

  ${
    cbv3.1 $e |- ( ph -> A. y ph ) $.
    cbv3.2 $e |- ( ps -> A. x ps ) $.
    cbv3.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition, that
       does not use ~ ax-12 . $)
    cbv3 $p |- ( A. x ph -> A. y ps ) $=
      ( wi wal imim2i a1i weq cbv1 id ax-gen mpg ) AAHZDIACIBDIHCQABCDAADIAEJBB
      CIHQFKCDLABHHQGKMQDANOP $.
      $( [5-Aug-1993] $)

    $( Rule used to change bound variables, using implicit substitition.  (The
       proof was shortened by Andrew Salmon, 25-May-2011.) $)
    cbv3ALT $p |- ( A. x ph -> A. y ps ) $=
      ( weq wal wi a1i cbv1 stdpc6 mpg ) DDHZDIACIBDIJCOABCDAADIJOEKBBCIJOFKCDH
      ABJJOGKLDMN $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    cbval.1 $e |- ( ph -> A. y ph ) $.
    cbval.2 $e |- ( ps -> A. x ps ) $.
    cbval.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.  (The
       proof was shortened by Andrew Salmon, 25-May-2011.) $)
    cbval $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbv3 wb equcoms biimprd impbii ) ACHBDHABCDEFCDIABGJKBAD
      CFEDCIABABLCDGMNKO $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    cbvex.1 $e |- ( ph -> A. y ph ) $.
    cbvex.2 $e |- ( ps -> A. x ps ) $.
    cbvex.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.
       (Revised by Mario Carneiro, 3-Feb-2015.) $)
    cbvex $p |- ( E. x ph <-> E. y ps ) $=
      ( wex hbex cv wceq wa wb bicomd equcoms equsex simpr eximi sylbir exlimi
      impbii ) ACHZBDHZAUCCBCDFIADJZCJZKZBLZDHUCBADCEBAMCDUEUDKZABGNOPUGBDUFBQR
      STBUBDADCEIBUHALZCHUBABCDFGPUIACUHAQRSTUA $.
      $( [3-Feb-2015] $) $( [5-Aug-1993] $)
  $}

  ${
    chv2.1 $e |- ( ps -> A. x ps ) $.
    chv2.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chv2.3 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by Raph Levien, 9-Jul-2003.) $)
    chvar $p |- ps $=
      ( weq biimpd a4im mpg ) ABCABCDECDHABFIJGK $.
      $( [9-Jul-2003] $)
  $}

  $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109,
     however we do not require ` z ` to be distinct from ` x ` and ` y `
     (making the proof longer).  (The proof was shortened by Andrew Salmon,
     25-May-2011.) $)
  equvini $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $=
    ( cv wceq wal wi wo wex ax12or equcomi alimi a9e jctir a1d 19.29 syl6 ax-mp
    wa jaoi eximi a1ii anc2ri 19.29r ax-8 anc2li equcoms com12 exim syl mpi a4s
    imim2i ) CDZADZEZCFZUNBDZEZCFZUOUREZVACFZGZCFZHZHVAUOUNEZUSSZCIZGZABCJUQVIV
    EUQVAVFCFZUSCIZSZVHUQVLVAUQVJVKUPVFCCAKZLCBMNOVFUSCPQUTVIVDUTVAVFCIZUTSVHUT
    VAVNUTVAVNUPCIZVNCAMZUPVFCVMUARUBUCVFUSCUDQVCVICVBVHVAVBVOVHVPVBUPVGGZCFVOV
    HGVAVQCUPVAVGVAVGGACVFVAUSACBUEUFUGUHLUPVGCUIUJUKUMULTTR $.
    $( [25-May-2011] $) $( [5-Aug-1993] $)

  $( A variable elimination law for equality with no distinct variable
     requirements.  (Compare ~ equvini .) $)
  equveli $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $=
    ( cv wb wal wi wa albiim wo ax12or equequ1 imbi12d a4s equid syl6bi adantrd
    wceq ax-4 jaoi dral2 a1bi biimpri dral1 mpi equcomi syl adantld hbequid a1i
    hba1 hbimd equtr ax-8 imim12d ax-gen 19.26 a4imt sylbir sylancl ax-mp sylbi
    a5i mpii ) CDZADZRZVEBDZRZECFVGVIGZCFZVIVGGZCFZHZVFVHRZVGVICIVGCFZVICFZVOVO
    CFGZCFZJZJVNVOGZABCKVPWAVTVPVKVOVMVPVKVFVFRZVOGZCFZVOVJWCCACVGVJWCECVGVGWBV
    IVOCAALCABLMNUAWCVOCVOWCWBVOAOZUBUCNPQVQWAVSVQVMVOVKVQVMVHVHRZVHVFRZGZBFZVO
    VLWHCBVIVLWHECVIVIWFVGWGCBBLCBALMNUDWIWGVOWIWFWGBOWHBSUEBAUFUGPUHVSVKVOVMVS
    VKWBVOWEVSWCWDGZCFZVGVJWCGGZCFZVKWCGZVRWJCVSWBVOCVRCUKWBWBCFGVSACUIUJVRCSUL
    VCWLCVGWBVGVIVOCAAUMCABUNUOUPWKWMHWJWLHCFWNWJWLCUQVJWCCAURUSUTVDQTTVAVB $.
    $( [3-Feb-2015] $) $( [1-Mar-2013] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Substitution (without distinct variables)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [ $. $( Left bracket $)
  $c / $. $( Division. $)
  $c ] $.  $( Right bracket $)

  $( --- Start of patch to prevent connective overloading $)
  ${
    $v A $.
    wsbc.cA $f class A $.
    $( Extend wff notation to include the proper substitution of a class for a
       set.  Read this notation as "the proper substitution of class ` A ` for
       set variable ` x ` in wff ` ph ` ."

       (The purpose of introducing ` wff [ A / x ] ph ` here is to allow us to
       express i.e.  "prove" the ~ wsb of predicate calculus in terms of the
       ~ wsbc of set theory, so that we don't "overload" its connectives with
       two syntax definitions.  This is done to prevent ambiguity that would
       complicate some Metamath parsers.  The class variable ` A ` is
       introduced temporarily for the purpose of this definition but otherwise
       not used in predicate calculus.) $)
    wsbc $a wff [ A / x ] ph $.
  $}

  $( Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").

     (Instead of introducing ~ wsb as an axiomatic statement, as was done in an
     older version of this database, we introduce it by "proving" a special
     case of set theory's more general ~ wsbc .  This lets us avoid overloading
     its connectives, thus preventing ambiguity that would complicate some
     Metamath parsers.  Note:  To see the proof steps of this syntax proof,
     type "show proof wsb /all" in the Metamath program.) $)
  wsb $p wff [ y / x ] ph $=
    ( cv wsbc ) ABCDE $.
    $( [24-Jan-2006] $)
  $( --- End of patch to prevent connective overloading $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include proper substitution (read "the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` ").

     After we introduce ~ cv and ~ wsbc in set theory, this syntax construction
     becomes redundant, since it can be derived with the proof
     "wph vx vy cv wsbc". @)
  wsb @a wff [ y / x ] ph @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Define proper substitution.  Remark 9.1 in [Megill] p. 447 (p. 15 of the
     preprint).  For our notation, we use ` [ y / x ] ph ` to mean "the wff
     that results when ` y ` is properly substituted for ` x ` in the wff
     ` ph ` ."  We can also use ` [ y / x ] ph ` in place of the "free for"
     side condition used in traditional predicate calculus; see, for example,
     ~ stdpc4 .

     Our notation was introduced in Haskell B. Curry's _Foundations of
     Mathematical Logic_ (1977), p. 316 and is frequently used in textbooks of
     lambda calculus and combinatory logic.  This notation improves the common
     but ambiguous notation, " ` ph ( y ) ` is the wff that results when ` y `
     is properly substituted for ` x ` in ` ph ( x ) ` ."  For example, if the
     original ` ph ( x ) ` is ` x = y ` , then ` ph ( y ) ` is ` y = y ` , from
     which we obtain that ` ph ( x ) ` is ` x = x ` .  So what exactly does
     ` ph ( x ) ` mean?  Curry's notation solves this problem.

     In most books, proper substitution has a somewhat complicated recursive
     definition with multiple cases based on the occurrences of free and bound
     variables in the wff.  Instead, we use a single formula that is exactly
     equivalent and gives us a direct definition.  We later prove that our
     definition has the properties we expect of proper substitution (see
     theorems ~ sbequ , ~ sbcom2 and ~ sbid2v ).

     Note that our definition is valid even when ` x ` and ` y ` are replaced
     with the same variable, as ~ sbid shows.  We achieve this by having ` x `
     free in the first conjunct and bound in the second.  We can also achieve
     this by using a dummy variable, as the alternate definition ~ dfsb7 shows
     (which some logicians may prefer because it doesn't mix free and bound
     variables).  Another version that mixes free and bound variables is
     ~ dfsb3 .  When ` x ` and ` y ` are distinct, we can express proper
     substitution with the simpler expressions of ~ sb5 and ~ sb6 .

     There are no restrictions on any of the variables, including what
     variables may occur in wff ` ph ` . $)
  df-sb $a |- ( [ y / x ] ph <->
              ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $.

  ${
    sbimi.1 $e |- ( ph -> ps ) $.
    $( Infer substitution into antecedent and consequent of an implication. $)
    sbimi $p |- ( [ y / x ] ph -> [ y / x ] ps ) $=
      ( weq wi wa wex wsb imim2i anim2i eximi anim12i df-sb 3imtr4i ) CDFZAGZQA
      HZCIZHQBGZQBHZCIZHACDJBCDJRUATUCABQEKSUBCABQELMNACDOBCDOP $.
      $( [25-Jun-1998] $)
  $}

  ${
    sbbii.1 $e |- ( ph <-> ps ) $.
    $( Infer substitution into both sides of a logical equivalence. $)
    sbbii $p |- ( [ y / x ] ph <-> [ y / x ] ps ) $=
      ( wsb biimpi sbimi biimpri impbii ) ACDFBCDFABCDABEGHBACDABEIHJ $.
      $( [5-Aug-1993] $)
  $}

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
  drsb1 $p |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) ) $=
    ( weq wal wi wa wex wsb wb equequ1 a4s imbi1d anbi1d drex1 anbi12d 3bitr4g
    df-sb ) BCEZBFZBDEZAGZUBAHZBIZHCDEZAGZUFAHZCIZHABDJACDJUAUCUGUEUIUAUBUFATUB
    UFKBBCDLMZNUDUHBCUAUBUFAUJOPQABDSACDSR $.
    $( [5-Aug-1993] $)

  $( One direction of a simplified definition of substitution. $)
  sb1 $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $=
    ( wsb weq wi wa wex df-sb simprbi ) ABCDBCEZAFKAGBHABCIJ $.
    $( [5-Aug-1993] $)

  $( One direction of a simplified definition of substitution. $)
  sb2 $p |- ( A. x ( x = y -> ph ) -> [ y / x ] ph ) $=
    ( weq wi wal wa wex wsb ax-4 equs4 df-sb sylanbrc ) BCDZAEZBFONAGBHABCIOBJA
    BCKABCLM $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution. $)
  sbequ1 $p |- ( x = y -> ( ph -> [ y / x ] ph ) ) $=
    ( weq wsb wa wi wex pm3.4 19.8a df-sb sylanbrc ex ) BCDZAABCEZNAFZNAGPBHONA
    IPBJABCKLM $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution. $)
  sbequ2 $p |- ( x = y -> ( [ y / x ] ph -> ph ) ) $=
    ( wsb weq wi wa wex df-sb simpl com12 syl5bi ) ABCDBCEZAFZMAGBHZGZMAABCIPMA
    NOJKL $.
    $( [5-Aug-1993] $)

  $( One of the two equality axioms of standard predicate calculus, called
     substitutivity of equality.  (The other one is ~ stdpc6 .)  Translated to
     traditional notation, it can be
     read:  " ` x = y -> ( ph ( x ` , ` x ) -> ph ( x ` , `
      y ) ) ` , provided that
     ` y ` is free for ` x ` in ` ph ( x ` , ` y ) ` ."  Axiom 7 of [Mendelson]
     p. 95. $)
  stdpc7 $p |- ( x = y -> ( [ x / y ] ph -> ph ) ) $=
    ( wsb wi sbequ2 equcoms ) ACBDAECBACBFG $.
    $( [15-Feb-2005] $)

  $( An equality theorem for substitution. $)
  sbequ12 $p |- ( x = y -> ( ph <-> [ y / x ] ph ) ) $=
    ( weq wsb sbequ1 sbequ2 impbid ) BCDAABCEABCFABCGH $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution.  (The proof was shortened by Andrew
     Salmon, 21-Jun-2011.) $)
  sbequ12r $p |- ( x = y -> ( [ x / y ] ph <-> ph ) ) $=
    ( wsb wb weq sbequ12 bicomd equcoms ) ACBDZAECBCBFAJACBGHI $.
    $( [26-Jun-2011] $) $( [6-Oct-2004] $)

  $( An equality theorem for substitution. $)
  sbequ12a $p |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) ) $=
    ( weq wsb sbequ12 wb equcoms bitr3d ) BCDAABCEACBEZABCFAJGCBACBFHI $.
    $( [5-Aug-1993] $)

  $( An identity theorem for substitution.  Remark 9.1 in [Megill] p. 447 (p.
     15 of the preprint). $)
  sbid $p |- ( [ x / x ] ph <-> ph ) $=
    ( wsb weq wb equid sbequ12 ax-mp bicomi ) AABBCZBBDAJEBFABBGHI $.
    $( [5-Aug-1993] $)

  $( The specialization axiom of standard predicate calculus.  It states that
     if a statement ` ph ` holds for all ` x ` , then it also holds for the
     specific case of ` y ` (properly) substituted for ` x ` .  Translated to
     traditional notation, it can be read:  " ` A. x ph ( x ) -> ph ( y ) ` ,
     provided that ` y ` is free for ` x ` in ` ph ( x ) ` ."  Axiom 4 of
     [Mendelson] p. 69. $)
  stdpc4 $p |- ( A. x ph -> [ y / x ] ph ) $=
    ( wal weq wi wsb ax-1 alimi sb2 syl ) ABDBCEZAFZBDABCGAMBALHIABCJK $.
    $( [5-Aug-1993] $)

  ${
    sbf.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution for a variable not free in a wff does not affect it. $)
    sbf $p |- ( [ y / x ] ph <-> ph ) $=
      ( wsb weq wex wa sb1 19.41 sylib simprd wal stdpc4 syl impbii ) ABCEZAQBC
      FZBGZAQRAHBGSAHABCIRABDJKLAABMQDABCNOP $.
      $( [17-Oct-2004] $) $( [5-Aug-1993] $)
  $}

  $( Substitution has no effect on a bound variable. $)
  sbf2 $p |- ( [ y / x ] A. x ph <-> A. x ph ) $=
    ( wal hba1 sbf ) ABDBCABEF $.
    $( [1-Jul-2005] $)

  ${
    sb6x.1 $e |- ( ph -> A. x ph ) $.
    $( Equivalence involving substitution for a variable not free.  (The proof
       was shortened by Andrew Salmon, 12-Aug-2011.) $)
    sb6x $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( cv wsbc wceq wi wal sbf biidd equsal bitr4i ) ABCEZFABENGZAHBIABCDJAABC
      DOAKLM $.
      $( [12-Aug-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    hbs1f.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (The proof was shortened by Andrew Salmon, 25-May-2011.) $)
    hbs1f $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb sbf hbxfrbi ) ABCEABABCDFDG $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  $( Substitution does not change an identical variable specifier. $)
  sbequ5 $p |- ( [ w / z ] A. x x = y <-> A. x x = y ) $=
    ( weq wal hbae sbf ) ABEAFCDABCGH $.
    $( [21-Dec-2004] $) $( [5-Aug-1993] $)

  $( Substitution does not change a distinctor. $)
  sbequ6 $p |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y ) $=
    ( weq wal wn hbnae sbf ) ABEAFGCDABCHI $.
    $( [14-May-2005] $) $( [5-Aug-1993] $)

  ${
    sbt.1 $e |- ph $.
    $( A substitution into a theorem remains true.  (See ~ chvar and ~ chvarv
       for versions using implicit substitition.)  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    sbt $p |- [ y / x ] ph $=
      ( wsb hbth sbf mpbir ) ABCEADABCABDFGH $.
      $( [25-May-2011] $) $( [21-Jan-2004] $)
  $}

  $( Substitution applied to an atomic wff. $)
  equsb1 $p |- [ y / x ] x = y $=
    ( weq wi wsb sb2 id mpg ) ABCZIDIABEAIABFIGH $.
    $( [5-Aug-1993] $)

  $( Substitution applied to an atomic wff. $)
  equsb2 $p |- [ y / x ] y = x $=
    ( weq wi wsb sb2 equcomi mpg ) ABCBACZDIABEAIABFABGH $.
    $( [5-Aug-1993] $)

  ${
    sbied.1 $e |- ( ph -> A. x ph ) $.
    sbied.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    sbied.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (The proof was shortened by Andrew Salmon,
       25-May-2011.) $)
    sbied $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb wex weq wa sb1 wb wi bi1 syl6 imp3a syld wal eximd syl5 19.9d com23
      bi2 alimd sb2 impbid ) ABDEIZCAUICDJZCUIDEKZBLZDJAUJBDEMAULCDFAUKBCAUKBCN
      ZBCOHBCPQRUAUBCADFGUCSACCDTZUIGAUNUKBOZDTUIACUODFAUKCBAUKUMCBOHBCUEQUDUFB
      DEUGQSUH $.
      $( [25-May-2011] $) $( [30-Jun-1994] $)
  $}

  ${
    sbie.1 $e |- ( ps -> A. x ps ) $.
    sbie.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution. $)
    sbie $p |- ( [ y / x ] ph <-> ps ) $=
      ( wi wsb wb id hbth wal a1i weq sbied ax-mp ) AAGZACDHBIAJZQABCDQCRKBBCLG
      QEMCDNABIGQFMOP $.
      $( [30-Jun-1994] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Theorems using axiom ax-11
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent. $)
  equs5a $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $=
    ( weq wal wa wi hba1 ax-11 imp exlimi ) BCDZACEZFLAGZBEZBNBHLMOABCIJK $.
    $( [2-Feb-2007] $)

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent. $)
  equs5e $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $=
    ( cv wceq wa wex wal wi 19.8a hbe1 syl anim2i eximi equs5a ) BDCDEZAFZBGPAC
    GZCHZFZBGPRIBHQTBASPARSACJACKLMNRBCOL $.
    $( [3-Feb-2015] $) $( [2-Feb-2007] $)

  $( A version of ~ sb4 that doesn't require a distinctor antecedent. $)
  sb4a $p |- ( [ y / x ] A. y ph -> A. x ( x = y -> ph ) ) $=
    ( wal wsb weq wa wex wi sb1 equs5a syl ) ACDZBCEBCFZMGBHNAIBDMBCJABCKL $.
    $( [2-Feb-2007] $)

  ${
    equs45f.1 $e |- ( ph -> A. y ph ) $.
    $( Two ways of expressing substitution when ` y ` is not free in
       ` ph ` . $)
    equs45f $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wa wex wi wal anim2i eximi equs5a syl equs4 impbii ) BCEZAFZBGZPAHB
      IZRPACIZFZBGSQUABATPDJKABCLMABCNO $.
      $( [25-Apr-2008] $)

    $( Equivalence for substitution when ` y ` is not free in ` ph ` . $)
    sb6f $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal sbimi sb4a syl sb2 impbii ) ABCEZBCFAGBHZNACHZBCEOAPBCDI
      ABCJKABCLM $.
      $( [30-Apr-2008] $)  $( [5-Aug-1993] $)

    $( Equivalence for substitution when ` y ` is not free in ` ph ` . $)
    sb5f $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6f equs45f bitr4i ) ABCEBCFZAGBHNAIBJABCDKABCDL
      M $.
      $( [18-May-2008] $)  $( [5-Aug-1993] $)
  $}

  $( One direction of a simplified definition of substitution that unlike ~ sb4
     doesn't require a distinctor antecedent. $)
  sb4e $p |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) ) $=
    ( wsb weq wa wex wi wal sb1 equs5e syl ) ABCDBCEZAFBGMACGHBIABCJABCKL $.
    $( [2-Feb-2007] $)

  $( Special case of a bound-variable hypothesis builder for substitution. $)
  hbsb2a $p |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph ) $=
    ( wal wsb weq wi sb4a sb2 a5i syl ) ACDBCEBCFAGZBDABCEZBDABCHLMBABCIJK $.
    $( [2-Feb-2007] $)

  $( Special case of a bound-variable hypothesis builder for substitution. $)
  hbsb2e $p |- ( [ y / x ] ph -> A. x [ y / x ] E. y ph ) $=
    ( wsb weq wex wi wal sb4e sb2 a5i syl ) ABCDBCEACFZGZBHMBCDZBHABCINOBMBCJKL
    $.
    $( [2-Feb-2007] $)

  ${
    hbsb3.1 $e |- ( ph -> A. y ph ) $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` . $)
    hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb wal sbimi hbsb2a syl ) ABCEZACFZBCEJBFAKBCDGABCHI $.
      $( [5-Aug-1993] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                  Predicate calculus with distinct variables
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive the axiom of distinct variables ax-16
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ps $.
    a4imv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( A version of ~ a4im with a distinct variable requirement instead of a
       bound variable hypothesis. $)
    a4imv $p |- ( A. x ph -> ps ) $=
      ( ax-17 a4im ) ABCDBCFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    $v f $.
    $( Define a temporary individual variable. $)
    aev.vf $f set f $.
    $d f u v $.  $d f u x y $.  $d u w $.
    $( A "distinctor elimination" lemma with no restrictions on variables in
       the consequent, proved without using ~ ax-16 .  (The proof was shortened
       by Andrew Salmon, 21-Jun-2011.) $)
    aev $p |- ( A. x x = y -> A. z w = v ) $=
      ( aev.vf vu weq wal hbae ax-8 a4imv alrimi equcomi alequcoms a5i alequcom
      syl6 3syl ) ABHZAIZDEHZCABCJUAFBHZFIZGEHZGIZUBUAUCFABFJTUCAFAFBKLMUDFGHZF
      IZEGHZEIUFUCUGFUGBFBFHZUGBGBGHUJGFHUGBGFKGFNRLOPUHUIEFGEJUGUIFEFEGKLMEGQS
      UEUBGDGDEKLSM $.
      $( [26-Jun-2011] $) $( [8-Nov-2006] $)
  $}

  ${
    $d x y $.  $d z ph $.
    $( Theorem showing that ~ ax-16 is redundant if ~ ax-17 is included in the
       axiom system.  The important part of the proof is provided by ~ aev .

       See ~ ax16ALT for an alternate proof that does not require ~ ax-10 or
       ~ ax-12 .

       This theorem should not be referenced in any proof.  Instead, use
       ~ ax-16 below so that theorems needing ~ ax-16 can be more easily
       identified. $)
    ax16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( vz weq wal wi aev ax-17 sbequ12 biimpcd alimd hbsb3 stdpc7 cbv3 syl6com
      wsb syl ) BCEBFBDEZDFZAABFZGBCDBDHATABDQZDFUAASUBDADIZSAUBABDJKLUBADBABDU
      CMUCADBNOPR $.
      $( [8-Nov-2006] $)
  $}

  ${
    $d x y $.
    $( Axiom of Distinct Variables.  The only axiom of predicate calculus
       requiring that variables be distinct (if we consider ~ ax-17 to be a
       metatheorem and not an axiom).  Axiom scheme C16' in [Megill] p. 448 (p.
       16 of the preprint).  It apparently does not otherwise appear in the
       literature but is easily proved from textbook predicate calculus by
       cases.  It is a somewhat bizarre axiom since the antecedent is always
       false in set theory, but nonetheless it is technically
       necessary as you can see from its uses.

       This axiom is redundant if we include ~ ax-17 ; see theorem ~ ax16 .
       Alternately, ~ ax-17 becomes logically redundant in the presence of this
       axiom, but without ~ ax-17 we lose the more powerful metalogic that
       results from being able to express the concept of a set variable not
       occurring in a wff (as opposed to just two set variables being
       distinct).  We retain ~ ax-16 here to provide logical completeness for
       systems with the simpler metalogic that results from omitting ~ ax-17 ,
       which might be easier to study for some theoretical purposes. $)
    ax-16 $a |- ( A. x x = y -> ( ph -> A. x ph ) ) $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  (This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.  Do not use it for later proofs - use ~ ax-17 instead, to
       avoid reference to the redundant axiom ~ ax-16 .) $)
    ax17eq $p |- ( x = y -> A. z x = y ) $=
      ( weq wal wi ax-12 ax-16 pm2.61ii ) CADCECBDCEABDZJCEFABCGJCAHJCBHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct. $)
    dveeq2 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq ax-17 equequ2 dvelimfALT ) CDEZCBEZABDIAFJDFDBCGH $.
      $( [2-Jan-2002] $)

    $( Version of ~ dveeq2 using ~ ax-16 instead of ~ ax-17 . $)
    dveeq2ALT $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq ax17eq equequ2 dvelimfALT ) CDECBEABDCDAFCBDFDBCGH $.
      $( [29-Apr-2008] $)
  $}


  ${
    $d x z $.  $d y z $.
    dvelimfALT2.1 $e |- ( ph -> A. x ph ) $.
    dvelimfALT2.2 $e |- ( ps -> A. z ps ) $.
    dvelimfALT2.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    dvelimfALT2.4 $e |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $.
    $( Proof of ~ dvelimf using ~ dveeq2 (shown as the last hypothesis) instead
       of ~ ax-12 .  This shows that ~ ax-12 could be replaced by ~ dveeq2 (the
       last hypothesis).  (Contributed by Andrew Salmon, 21-Jul-2011.) $)
    dvelimfALT2 $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( cv wceq wal wn wi ax-17 hbn1 a1i hbimd hbald equsal albii 3imtr3g ) CJD
      JZKZCLMZEJUCKZANZELZUHCLBBCLUEUGCEUEEOUEUFACUDCPIAACLNUEFQRSABEDGHTZUHBCU
      IUAUB $.
      $( [21-Jul-2011] $)
  $}

  ${
    $d z x $.
    $( A lemma for proving conditionless ZFC axioms. $)
    nd5 $p |- ( -. A. y y = x -> ( z = y -> A. x z = y ) ) $=
      ( cv wceq wal wi dveeq2 nalequcoms ) CDBDEZJAFGABABCHI $.
      $( [8-Jan-2002] $)
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90. $)
    exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( ax-17 exlimd ) ABCDADFCDFEG $.
      $( [27-Apr-1994] $)
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11v2.1 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
    $( Recovery of ~ ax11o from ~ ax11v without using ~ ax-11 .  The hypothesis
       is even weaker than ~ ax11v , with ` z ` both distinct from ` x ` _and_
       not occurring in ` ph ` .  Thus the hypothesis provides an alternate
       axiom that can be used in place of ~ ax11o . $)
    ax11v2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wex wi a9e wa wb equequ2 adantl dveeq2 imp hba1 imbi1d a4s
      albid syl imbi2d imbi12d mpbii ex exlimdv mpi ) BCFZBGHZDCFZDIUIAUIAJZBGZ
      JZJZDCKUJUKUODUJUKUOUJUKLZBDFZAUQAJZBGZJZJUOEUPUQUIUTUNUKUQUIMUJDCBNZOUPU
      SUMAUPUKBGZUSUMMUJUKVBBCDPQVBURULBUKBRUKURULMBUKUQUIAVASTUAUBUCUDUEUFUGUH
      $.
      $( [2-Feb-2007] $)
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11a2.1 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
    $( Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 .  The
       hypothesis is even weaker than ~ ax-11 , with ` z ` both distinct from
       ` x ` and not occurring in ` ph ` .  Thus the hypothesis provides an
       alternate axiom that can be used in place of ~ ax11o .  As theorem
       ~ ax11 shows, the distinct variable conditions are optional.  An open
       problem is whether ~ ax11o can be derived from ~ ax-11 without relying
       on ~ ax-17 . $)
    ax11a2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( wal weq wi ax-17 syl5 ax11v2 ) ABCDAADFBDGZLAHBFADIEJK $.
      $( [2-Feb-2007] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive the obsolete axiom of variable substitution ax-11o
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( Derivation of set.mm's original ~ ax-11o from the shorter ~ ax-11 that
       has replaced it.

       An open problem is whether this theorem can be proved without relying on
       ~ ax-16 or ~ ax-17 .

       Another open problem is whether this theorem can be proved without
       relying on ~ ax-12 (see note in ~ a12study ).

       Theorem ~ ax11 shows the reverse derivation of ~ ax-11 from ~ ax-11o .

       Normally, ~ ax11o should be used rather than ~ ax-11o , except by
       theorems specifically studying the latter's properties. $)
    ax11o $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( vz ax-11 ax11a2 ) ABCDABDEF $.
      $( [3-Feb-2007] $)
  $}

  $( Axiom ~ ax-11o ("o" for "old") was the original version of ~ ax-11 ,
     before it was discovered (in Jan. 2007) that the shorter ~ ax-11 could
     replace it.  It appears as Axiom scheme C15' in [Megill] p. 448 (p. 16 of
     the preprint).  It is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of
     [Monk2] p. 105, from which it can be proved by cases.  To understand this
     theorem more easily, think of " ` -. A. x x = y -> ` ..." as informally
     meaning "if ` x ` and ` y ` are distinct variables then..."  The
     antecedent becomes false if the same variable is substituted for ` x ` and
     ` y ` , ensuring the theorem is sound whenever this is the case.  In some
     later theorems, we call an antecedent of the form ` -. A. x x = y ` a
     "distinctor."

     This axiom is redundant, as shown by theorem ~ ax11o .

     Normally, ~ ax11o should be used rather than ~ ax-11o , except by theorems
     specifically studying the latter's properties. $)
  ax-11o $a |- ( -. A. x x = y ->
             ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.

  $( Rederivation of axiom ~ ax-11 from the orginal version, ~ ax-11o .  See
     theorem ~ ax11o for the derivation of ~ ax-11o from ~ ax-11 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-11
     above so that uses of ~ ax-11 can be more easily identified. $)
  ax11 $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wi biidd dral1 ax-1 alimi syl6bir a1d wn ax-4 ax-11o syl7 pm2.61i
    ) BCDZBEZRACEZRAFZBEZFZFSUCRSTABEUBAABCSAGHAUABARIJKLTASMRUBACNABCOPQ $.
    $( [22-Jan-2007] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
     Theorems without distinct variables that use axiom ax-11o
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A bidirectional version of ~ ax-11o . $)
  ax11b $p |- ( ( -. A. x x = y /\ x = y ) ->
              ( ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi ax-11o imp ax-4 com12 adantl impbid ) BCDZBEFZOGAOAHZBEZ
    POARHABCIJORAHPROAQBKLMN $.
    $( [30-Jun-2006] $)

  $( Lemma used in proofs of substitution properties. $)
  equs5 $p |- ( -. A. x x = y ->
             ( E. x ( x = y /\ ph ) -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi hbnae hba1 ax11o imp3a exlimd ) BCDZBEFZNAGNAHZBEZBBCBIP
    BJONAQABCKLM $.
    $( [5-Aug-1993] $)

  $( One direction of a simplified definition of substitution when variables
     are distinct. $)
  sb3 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) ) $=
    ( weq wal wn wa wex wi wsb equs5 sb2 syl6 ) BCDZBEFNAGBHNAIBEABCJABCKABCLM
    $.
    $( [5-Aug-1993] $)

  $( One direction of a simplified definition of substitution when variables
     are distinct. $)
  sb4 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x ( x = y -> ph ) ) ) $=
    ( wsb weq wa wex wal wn wi sb1 equs5 syl5 ) ABCDBCEZAFBGNBHINAJBHABCKABCLM
    $.
    $( [5-Aug-1993] $)

  $( Simplified definition of substitution when variables are distinct. $)
  sb4b $p |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wsb wi sb4 sb2 impbid1 ) BCDZBEFABCGLAHBEABCIABCJK $.
    $( [27-May-1997] $)

  $( An alternate definition of proper substitution that, like ~ df-sb , mixes
     free and bound variables to avoid distinct variable requirements. $)
  dfsb2 $p |- ( [ y / x ] ph <->
              ( ( x = y /\ ph ) \/ A. x ( x = y -> ph ) ) ) $=
    ( wsb weq wa wi wal wo sbequ2 a4s ax-4 jctild orc wn sb4 olc pm2.61i sbequ1
    syl6 imp sb2 jaoi impbii ) ABCDZBCEZAFZUFAGBHZIZUFBHZUEUIGUJUEUGUIUJUEAUFUF
    UEAGBABCJKUFBLMUGUHNTUJOUEUHUIABCPUHUGQTRUGUEUHUFAUEABCSUAABCUBUCUD $.
    $( [17-Feb-2005] $)

  $( An alternate definition of proper substitution ~ df-sb that uses only
     primitive connectives (no defined terms) on the right-hand side. $)
  dfsb3 $p |- ( [ y / x ] ph <->
              ( ( x = y -> -. ph ) -> A. x ( x = y -> ph ) ) ) $=
    ( weq wa wi wal wo wn wsb df-or dfsb2 imnan imbi1i 3bitr4i ) BCDZAEZPAFBGZH
    QIZRFABCJPAIFZRFQRKABCLTSRPAMNO $.
    $( [6-Mar-2007] $)

  $( Bound-variable hypothesis builder for substitution. $)
  hbsb2 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $=
    ( weq wal wn wsb wi sb4 sb2 a5i syl6 ) BCDZBEFABCGZMAHZBENBEABCIONBABCJKL
    $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution. $)
  sbequi $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    ( weq wal wsb wi wn wa wex hbsb2 stdpc7 sbequ1 sylan9 ex a4s adantr biimpd
    drsb1 equvini eximi syl 19.35 sylib hbnae 19.9d syl9 com23 sbequ2 alequcoms
    sylan9r syld pm2.61ii ) DBEZDFZDCEZDFZBCEZADBGZADCGZHZHUPIZUSURIZVBVCUSVDVB
    HVCUSJUTVADKZVDVAVCUTUTDFZUSVEADBLUSVBDKZVFVEHUSBDEZUQJZDKVGBCDUAVIVBDVHUTA
    UQVAABDMADCNZOUBUCUTVADUDUEOVAVDDDCDUFADCLUGUHPUIUPUSVBUPUSJUTAVAUPUTAHZUSU
    OVKDADBUJQRUSAABCGZUPVAABCNVLVAHBDVHBFVLVAABDCTSUKULUMPURUSVBURUSJUTAVAURUT
    ACBGZUSAURUTVMADCBTSABCMOURAVAHZUSUQVNDVJQRUMPUN $.
    $( [5-Aug-1993] $)

  $( An equality theorem for substitution.  Used in proof of Theorem 9.7 in
     [Megill] p. 449 (p. 16 of the preprint). $)
  sbequ $p |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( weq wsb sbequi wi equcoms impbid ) BCEADBFZADCFZABCDGLKHCBACBDGIJ $.
    $( [5-Aug-1993] $)

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint). $)
  drsb2 $p |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( cv wceq wsbc wb sbequ a4s ) BEZCEZFADKGADLGHBABCDIJ $.
    $( [27-Feb-2005] $)

  $( Negation inside and outside of substitution are equivalent. $)
  sbn $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $=
    ( wn wsb weq wal wi sbequ2 nsyld a4s sb4 wa wex sb1 equs3 sylib syl6 sylibr
    con2i pm2.61i sbequ1 con3rr3 sb2 notnot sbbii con3i df-sb sylanbrc impbii )
    ADZBCEZABCEZDZBCFZBGZULUNHZUOUQBUOULAUMUKBCIABCIJKUPDULUOUKHZBGZUNUKBCLUMUS
    UMUOAMBNUSDABCOABCPQTRUAUNURUOUKMBNZULUOAUMABCUBUCUNUOUKDZHBGZDUTVBUMVBVABC
    EUMVABCUDAVABCAUEUFSUGUKBCPSUKBCUHUIUJ $.
    $( [5-Aug-1993] $)

  $( Removal of implication from substitution. $)
  sbi1 $p |- ( [ y / x ] ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( weq wal wi wsb sbequ2 syl5d sbequ1 syl6d a4s sb4 ax-2 al2imi syl6 pm2.61i
    wn sb2 ) CDEZCFZABGZCDHZACDHZBCDHZGGZUAUGCUAUDUEBUFUAUEAUDBACDIUCCDIJBCDKLM
    UBSZUEUAAGZCFZUDUFACDNUHUDUAUCGZCFZUJUFGUCCDNULUJUABGZCFUFUKUIUMCUAABOPBCDT
    QQJR $.
    $( [5-Aug-1993] $)

  $( Introduction of implication into substitution. $)
  sbi2 $p |- ( ( [ y / x ] ph -> [ y / x ] ps ) -> [ y / x ] ( ph -> ps ) ) $=
    ( wsb wi wn sbn pm2.21 sbimi sylbir ax-1 ja ) ACDEZBCDEABFZCDEZNGAGZCDEPACD
    HQOCDABIJKBOCDBALJM $.
    $( [5-Aug-1993] $)

  $( Implication inside and outside of substitution are equivalent. $)
  sbim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wsb sbi1 sbi2 impbii ) ABECDFACDFBCDFEABCDGABCDHI $.
    $( [5-Aug-1993] $)

  $( Logical OR inside and outside of substitution are equivalent. $)
  sbor $p |- ( [ y / x ] ( ph \/ ps ) <-> ( [ y / x ] ph \/ [ y / x ] ps ) ) $=
    ( wn wi wsb wo sbim sbn imbi1i bitri df-or sbbii 3bitr4i ) AEZBFZCDGZACDGZE
    ZBCDGZFZABHZCDGSUAHRPCDGZUAFUBPBCDIUDTUAACDJKLUCQCDABMNSUAMO $.
    $( [29-Sep-2002] $)

  ${
    sbrim.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution with a variable not free in antecedent affects only the
       consequent. $)
    sbrim $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $=
      ( wi wsb sbim sbf imbi1i bitri ) ABFCDGACDGZBCDGZFAMFABCDHLAMACDEIJK $.
      $( [5-Aug-1993] $)
  $}

  ${
    sblim.1 $e |- ( ps -> A. x ps ) $.
    $( Substitution with a variable not free in consequent affects only the
       antecedent. $)
    sblim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $=
      ( wi wsb sbim sbf imbi2i bitri ) ABFCDGACDGZBCDGZFLBFABCDHMBLBCDEIJK $.
      $( [14-Nov-2013] $)
  $}

  $( Conjunction inside and outside of a substitution are equivalent. $)
  sban $p |- ( [ y / x ] ( ph /\ ps ) <-> ( [ y / x ] ph /\ [ y / x ] ps ) ) $=
    ( wn wi wsb wa sbn sbim imbi2i bitri xchbinx df-an sbbii 3bitr4i ) ABEZFZEZ
    CDGZACDGZBCDGZEZFZEABHZCDGUAUBHTRCDGZUDRCDIUFUAQCDGZFUDAQCDJUGUCUABCDIKLMUE
    SCDABNOUAUBNP $.
    $( [5-Aug-1993] $)

  $( Conjunction inside and outside of a substitution are equivalent. $)
  sb3an $p |- ( [ y / x ] ( ph /\ ps /\ ch ) <->
              ( [ y / x ] ph /\ [ y / x ] ps /\ [ y / x ] ch ) ) $=
    ( w3a wsb wa df-3an sbbii sban anbi1i bitr4i 3bitri ) ABCFZDEGABHZCHZDEGPDE
    GZCDEGZHZADEGZBDEGZSFZOQDEABCIJPCDEKTUAUBHZSHUCRUDSABDEKLUAUBSIMN $.
    $( [14-Dec-2006] $)

  $( Equivalence inside and outside of a substitution are equivalent. $)
  sbbi $p |- ( [ y / x ] ( ph <-> ps )
     <-> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wb wsb wi wa dfbi2 sbbii sbim anbi12i sban 3bitr4i bitri ) ABEZCDFABGZBAG
    ZHZCDFZACDFZBCDFZEZPSCDABIJQCDFZRCDFZHUAUBGZUBUAGZHTUCUDUFUEUGABCDKBACDKLQR
    CDMUAUBINO $.
    $( [5-Aug-1993] $)

  ${
    sblbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce left biconditional inside of a substitution. $)
    sblbis $p |- ( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) ) $=
      ( wb wsb sbbi bibi2i bitri ) CAGDEHCDEHZADEHZGLBGCADEIMBLFJK $.
      $( [19-Aug-1993] $)
  $}

  ${
    sbrbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution. $)
    sbrbis $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> [ y / x ] ch ) ) $=
      ( wb wsb sbbi bibi1i bitri ) ACGDEHADEHZCDEHZGBMGACDEILBMFJK $.
      $( [18-Aug-1993] $)
  $}

  ${
    sbrbif.1 $e |- ( ch -> A. x ch ) $.
    sbrbif.2 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution. $)
    sbrbif $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb wsb sbrbis sbf bibi2i bitri ) ACHDEIBCDEIZHBCHABCDEGJNCBCDEFKLM $.
      $( [18-Aug-1993] $)
  $}

  $( A specialization theorem. $)
  a4sbe $p |- ( [ y / x ] ph -> E. x ph ) $=
    ( wsb wn wal wex stdpc4 sbn sylib con2i df-ex sylibr ) ABCDZAEZBFZEABGPNPOB
    CDNEOBCHABCIJKABLM $.
    $( [5-Aug-1993] $)

  $( Specialization of implication.  (The proof was shortened by Andrew Salmon,
     25-May-2011.) $)
  a4sbim $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wal wsb stdpc4 sbi1 syl ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.
    $( [25-May-2011] $) $( [5-Aug-1993] $)

  $( Specialization of biconditional. $)
  a4sbbi $p |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wb wal wsb stdpc4 sbbi sylib ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.
    $( [5-Aug-1993] $)

  ${
    sbbid.1 $e |- ( ph -> A. x ph ) $.
    sbbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional. $)
    sbbid $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $=
      ( wb wal wsb alrimi a4sbbi syl ) ABCHZDIBDEJCDEJHANDFGKBCDELM $.
      $( [5-Aug-1993] $)
  $}

  $( Elimination of equality from antecedent after substitution. $)
  sbequ8 $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $=
    ( wsb weq wi equsb1 a1bi sbim bitr4i ) ABCDZBCEZBCDZKFLAFBCDMKBCGHLABCIJ $.
    $( [5-Aug-1993] $)

  $( Substitution has no effect on a non-free variable. $)
  sbf3t $p |- ( A. x ( ph -> A. x ph ) -> ( [ y / x ] ph <-> ph ) ) $=
    ( wal wi wsb a4sbim sbf2 ax-4 sylbi syl6 stdpc4 imim2i a4s impbid ) AABDZEZ
    BDZABCFZARSPBCFZAAPBCGTPAABCHABIJKQASEBPSAABCLMNO $.
    $( [30-May-2009] $)

  ${
    hbsb4.1 $e |- ( ph -> A. z ph ) $.
    $( A variable not free remains so after substitution with a distinct
       variable. $)
    hbsb4 $p |- ( -. A. z z = y -> ( [ y / x ] ph -> A. z [ y / x ] ph ) ) $=
      ( weq wal wn wsb wi wb equequ1 a4s dral1 notbid hbsb2 alimi hbnae pm2.61i
      hban ax10o alequcoms sylbid hbae ax-4 sbequ2 sbequ1 al2imi syl5 syld 3syl
      syl9r wa a1d sb4 ax-12 imp a1i hbimd alimd sb2 a7s syl6 syl9 ex ) DBFZDGZ
      DCFZDGZHZABCIZVKDGZJZJVGVJBCFZBGZHZVMVGVIVOVHVNDBVFVHVNKDDBCLMNOVPVKVKBGZ
      VGVLABCPVQVLJBDVKBDUAUBULUCVGHZVJVMVOVRVJUMZVMJVOVMVSVOVODGVNDGZVMBCDUDVO
      VNDVNBUEQVTVKAVLVNVKAJDABCUFMAADGZVTVLEVNAVKDABCUGUHUIUJUKUNVPVKVNAJZBGZV
      SVLABCUOVSWCWBDGZBGVLVSWBWDBVRVJBDBBRDCBRTVSVNADVRVJDDBDRDCDRTVRVJVNVTJBC
      DUPUQAWAJVSEURUSUTWBVLDBWCVKDABCVAQVBVCVDSVES $.
      $( [5-Aug-1993] $)
  $}

  $( A variable not free remains so after substitution with a distinct variable
     (closed form of ~ hbsb4 ).  (The proof was shortened by Andrew Salmon,
     25-May-2011.) $)
  hbsb4t $p |- ( A. x A. z ( ph -> A. z ph ) ->
               ( -. A. z z = y -> ( [ y / x ] ph -> A. z [ y / x ] ph ) ) ) $=
    ( weq wal wn wsb wi hba1 hbsb4 a4sbim a4s ax-4 sbimi alimi a1i imim12d syl5
    a7s ) DCEDFGADFZBCHZUBDFZIZAUAIZDFBFABCHZUFDFZIZUABCDADJKUEUDUHIDBUEBFZDFZU
    FUBUCUGUIUFUBIDAUABCLMUCUGIUJUBUFDUAABCADNOPQRTS $.
    $( [25-May-2011] $) $( [7-Apr-2004] $)

  ${
    dvelimf.1 $e |- ( ph -> A. x ph ) $.
    dvelimf.2 $e |- ( ps -> A. z ps ) $.
    dvelimf.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim without any variable restrictions. $)
    dvelimf $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wsb hbsb4 sbie albii 3imtr3g ) CDICJKAEDLZQCJBBCJAEDCFMABEDG
      HNZQBCROP $.
      $( [1-Oct-2002] $)
  $}

  ${
    dvelimdf.1 $e |- ( ph -> A. x ph ) $.
    dvelimdf.2 $e |- ( ph -> A. z ph ) $.
    dvelimdf.3 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    dvelimdf.4 $e |- ( ph -> ( ch -> A. z ch ) ) $.
    dvelimdf.5 $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
    $( Deduction form of ~ dvelimf .  This version may be useful if we want to
       avoid ~ ax-17 and use ~ ax-16 instead. $)
    dvelimdf $p |- ( ph -> ( -. A. x x = y -> ( ch -> A. x ch ) ) ) $=
      ( weq wal wn wi wa wsb alrimi wb adantr 2alimi hbsb4t sbied albid 3imtr3d
      3syl imp ex ) ADELDMNZCCDMZOAUIPBFEQZUKDMZCUJAUIUKULOZAADMZFMBBDMOZDMFMUI
      UMOAUNFHGRAUOFDIUABFEDUBUFUGAUKCSUIABCFEHJKUCZTAULUJSUIAUKCDGUPUDTUEUH $.
      $( [7-Apr-2004] $)
  $}

  $( A composition law for substitution. $)
  sbco $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
    ( wsb wb weq equsb2 sbequ12 bicomd sbimi ax-mp sbbi mpbi ) ACBDZAEZBCDZNBCD
    ABCDECBFZBCDPBCGQOBCQANACBHIJKNABCLM $.
    $( [5-Aug-1993] $)

  ${
    sbid2.1 $e |- ( ph -> A. x ph ) $.
    $( An identity law for substitution. $)
    sbid2 $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( wsb sbco sbf bitri ) ACBEBCEABCEAABCFABCDGH $.
      $( [5-Aug-1993] $)
  $}

  $( An idempotent law for substitution.  (The proof was shortened by Andrew
     Salmon, 25-May-2011.) $)
  sbidm $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $=
    ( wsb wb weq equsb2 sbequ12r sbimi ax-mp sbbi mpbi ) ABCDZAEZBCDZMBCDMECBFZ
    BCDOBCGPNBCACBHIJMABCKL $.
    $( [25-May-2011] $) $( [30-Jun-1994] $)

  ${
    sbco2.1 $e |- ( ph -> A. z ph ) $.
    $( A composition law for substitution. $)
    sbco2 $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( weq wal wsb wb sbid2 sbequ syl5bbr sbequ12 bitr3d a4s hbnae hbsb3 hbsb4
      wn wi a1i sbied bicomd pm2.61i ) BCFZBGZABDHZDCHZABCHZIZUEUJBUEAUHUIAUGDB
      HUEUHADBEJUGBCDKLZABCMNOUFSZUIUHULAUHBCBCBPUGDCBABDEQRUEAUHITULUKUAUBUCUD
      $.
      $( [30-Jun-1994] $)
  $}

  ${
    sbco2d.1 $e |- ( ph -> A. x ph ) $.
    sbco2d.2 $e |- ( ph -> A. z ph ) $.
    sbco2d.3 $e |- ( ph -> ( ps -> A. z ps ) ) $.
    $( A composition law for substitution. $)
    sbco2d $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $=
      ( wsb wi hbim1 sbco2 sbrim sbbii bitri 3bitr3i pm5.74ri ) ABCEIZEDIZBCDIZ
      ABJZCEIZEDIZUACDIASJZATJUACDEABEGHKLUCARJZEDIUDUBUEEDABCEFMNAREDGMOABCDFM
      PQ $.
      $( [5-Aug-1993] $)
  $}

  $( A composition law for substitution. $)
  sbco3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $=
    ( weq wal wsb wb drsb1 sbequ12a alimi a4sbbi syl bitr3d wn sbco sbbii hbnae
    hbsb2 sbco2d syl5rbbr pm2.61i ) BCEZBFZABCGZCDGZACBGZBDGZHUDUEBDGZUFUHUEBCD
    IUDUEUGHZBFUIUHHUCUJBABCJKUEUGBDLMNUHUECBGZBDGUDOZUFUKUGBDACBPQULUECDBBCCRB
    CBRABCSTUAUB $.
    $( [5-Aug-1993] $)

  $( A commutativity law for substitution. $)
  sbcom $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
    ( weq wal wsb wb wn wa hbae sbbid bitr3d hbnae hban albid sb4b sbequ12 a4s
    wi drsb1 adantr ax-12 imp alimi 19.21t 3syl adantrr alcom bi2.04 nalequcoms
    albii syl5bb adantrl imbi2d sylan9bbr adantl sylan9bb pm2.61ian ex pm2.61ii
    3bitr4d ) BCEZBFZDCEZDFZABCGZDCGZADCGZBCGZHZVDIZVFIZVKBDEBFZVLVMJZVKVNVKVOV
    NVGBCGVHVJVGBDCUAVNVGVIBCBDBKABDCUALMUBVNIZVOJZVEVCATZBFZTZDFZVCVEATZDFZTZB
    FZVHVJVQVEVRTZBFZDFZWAWEVPVLWHWAHVMVPVLJZWGVTDVPVLDBDDNZBCDNZOWIWIBFVEVEBFT
    ZBFWGVTHVPVLBBDBNZBCBNOWIWLBVPVLWLDCBUCUDUEVEVRBUFUGPUHVPVMWHWEHVLWHWFDFZBF
    VPVMJZWEWFDBUIWOWNWDBVPVMBWMDCBNZOWNVCWBTZDFZWOWDWFWQDVEVCAUJULWOWODFVCVCDF
    TZDFWRWDHVPVMDWJDCDNOWOWSDVPVMWSVMWSTDBBCDUCUKUDUEVCWBDUFUGUMPUMUNMVOVHWAHV
    PVMVHVEVGTZDFVLWAVGDCQVLWTVTDWKVLVGVSVEABCQUOPUPUQVOVJWEHVPVLVJVCVITZBFVMWE
    VIBCQVMXAWDBWPVMVIWCVCADCQUOPURUQVBUSUTVDVIVHVJVDAVGDCBCDKVCAVGHBABCRSLVCVI
    VJHBVIBCRSMVFVGVHVJVEVGVHHDVGDCRSVFAVIBCDCBKVEAVIHDADCRSLMVA $.
    $( [27-May-1997] $)

  ${
    sb5rf.1 $e |- ( ph -> A. y ph ) $.
    $( Reversed substitution.  (The proof was shortened by Andrew Salmon,
       25-May-2011.) $)
    sb5rf $p |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) ) $=
      ( weq wsb wa wex sbid2 sb1 sylbir stdpc7 imp exlimi impbii ) ACBEZABCFZGZ
      CHZAQCBFSACBDIQCBJKRACDPQAACBLMNO $.
      $( [25-May-2011] $) $( [3-Feb-2005] $)

    $( Reversed substitution.  (The proof was shortened by Andrew Salmon,
       25-May-2011.) $)
    sb6rf $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $=
      ( weq wsb wi wal sbequ1 equcoms com12 alrimi sb2 sbid2 sylib impbii ) ACB
      EZABCFZGZCHZASCDQARARGBCABCIJKLTRCBFARCBMACBDNOP $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    sb8.1 $e |- ( ph -> A. y ph ) $.
    $( Substitution of variable in universal quantifier.  (The proof was
       shortened by Andrew Salmon, 25-May-2011.) $)
    sb8 $p |- ( A. x ph <-> A. y [ y / x ] ph ) $=
      ( wal wsb hbal stdpc4 alrimi hbsb3 stdpc7 cbv3 impbii ) ABEZABCFZCENOCACB
      DGABCHIOACBABCDJDACBKLM $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)
  $}

  ${
    sb8e.1 $e |- ( ph -> A. y ph ) $.
    $( Substitution of variable in existential quantifier. $)
    sb8e $p |- ( E. x ph <-> E. y [ y / x ] ph ) $=
      ( wn wal wsb wex hbn sb8 sbn albii bitri notbii df-ex 3bitr4i ) AEZBFZEAB
      CGZEZCFZEABHSCHRUARQBCGZCFUAQBCACDIJUBTCABCKLMNABOSCOP $.
      $( [12-Aug-1993] $)
  $}

  $( Commutation of quantification and substitution variables. $)
  sb9i $p |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph ) $=
    ( weq wal wi drsb1 drsb2 bitr3d dral1 biimprd wn hbsb2 al2imi hbnaes stdpc4
    wsb sbco sylib alimi a7s syl6 pm2.61i ) CBDCEZACBQZBEZABCQZCEZFUDUHUFUGUECB
    UDACCQUGUEACBCGACBCHIJKUDLZUFUECEZBEZUHUFUKFCBBUIUEUJBACBMNOUEUHCBUFUGCUFUE
    BCQUGUEBCPABCRSTUAUBUC $.
    $( [5-Aug-1993] $)

  $( Commutation of quantification and substitution variables. $)
  sb9 $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $=
    ( wsb wal sb9i impbii ) ACBDBEABCDCEABCFACBFG $.
    $( [5-Aug-1993] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Predicate calculus with distinct variables (cont.)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    $( This is a version of ~ ax-11o when the variables are distinct.  Axiom
       (C8) of [Monk2] p. 105.  See theorem ~ ax11v2 for the rederivation of
       ~ ax-11o from this theorem. $)
    ax11v $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wal wi ax-1 ax-16 syl5 a1d ax11o pm2.61i ) BCDZBEZMAMAFZBEZFZFNQMAO
      NPAMGOBCHIJABCKL $.
      $( [5-Aug-1993] $)

    $( Two equivalent ways of expressing the proper substitution of ` y ` for
       ` x ` in ` ph ` , when ` x ` and ` y ` are distinct.  Theorem 6.2 of
       [Quine] p. 40.  The proof does not involve ~ df-sb . $)
    sb56 $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wal hba1 ax11v ax-4 com12 impbid equsex ) ABCDZAEZBFZBCNBGMAOABC
      HOMANBIJKL $.
      $( [14-Apr-2008] $)

    $( Equivalence for substitution.  Compare Theorem 6.2 of [Quine] p. 40.
       Also proved as Lemmas 16 and 17 of [Tarski] p. 70. $)
    sb6 $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wa wex wal wsb sb56 anbi2i df-sb ax-4 pm4.71ri 3bitr4i ) BCDZAEZ
      PAFBGZFQQBHZFABCISRSQABCJKABCLSQQBMNO $.
      $( [14-Apr-2008] $) $( [18-Aug-1993] $)

    $( Equivalence for substitution.  Similar to Theorem 6.1 of [Quine]
       p. 40. $)
    sb5 $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6 sb56 bitr4i ) ABCDBCEZAFBGMAHBIABCJABCKL $.
      $( [14-Apr-2008] $) $( [18-Aug-1993] $)
  $}

  ${
    $d x y z $.  $d z ph $.
    ax16i.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    ax16i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference with ~ ax-16 as its conclusion, that doesn't require ~ ax-10 ,
       ~ ax-11 , or ~ ax-12 for its proof.  The hypotheses may be eliminable
       without one or more of these axioms in special cases. $)
    ax16i $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( weq wal wi ax-17 ax-8 cbv3 a4imv equid1 mpi syl syl5com alimd mpcom
      alimi biimpcd biimprd syl6com ) CDHZCIZCEHZEIZAACIZJUFEDHZEIZUHUEUJCEUEEK
      ZUJCKCEDLMUKECHZEIZUHUEUKUNUJUEECECDLNUEUJUMEULUEDCHZUJUMUECCHUOCOCDCLPUJ
      DEHZUOUMJUJEEHZUPEOZEDELPDECLQRSTUMUGEUMUQUGURECELPZUAQQAUHBEIUIAUGBEAEKZ
      UGABFUBSBAECGUTUMUGBAJUSUGABFUCQMUDQ $.
      $( [20-May-2008] $)
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Version of ~ ax16 that doesn't require ~ ax-10 or ~ ax-12 for its
       proof. $)
    ax16ALT $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( vz wsb sbequ12 ax-17 hbsb3 ax16i ) AABDEBCDABDFABDADGHI $.
      $( [17-May-2008] $)
  $}

  ${
    $d x ps $.
    a4v.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Specialization, using implicit substitition. $)
    a4v $p |- ( A. x ph -> ps ) $=
      ( weq biimpd a4imv ) ABCDCDFABEGH $.
      $( [30-Aug-1993] $)
  $}

  ${
    $d x ph $.
    a4imev.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Distinct-variable version of ~ a4ime . $)
    a4imev $p |- ( ph -> E. x ps ) $=
      ( ax-17 a4ime ) ABCDACFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.
    a4eiv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    a4eiv.2 $e |- ps $.
    $( Inference from existential specialization, using implicit
       substitition. $)
    a4eiv $p |- E. x ph $=
      ( wex weq biimprd a4imev ax-mp ) BACGFBACDCDHABEIJK $.
      $( [19-Aug-1993] $)
  $}

  ${
    $d x z $.  $d y z $.
    $( A variable introduction law for equality.  Lemma 15 of [Monk2]
       p. 109. $)
    equvin $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $=
      ( weq wa wex equvini ax-17 equtr imp exlimi impbii ) ABDZACDZCBDZEZCFABCG
      PMCMCHNOMACBIJKL $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.
    $( A generalization of axiom ~ ax-16 .  (The proof was shortened by Andrew
       Salmon, 25-May-2011.) $)
    a16g $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( weq wal aev ax-16 biidd dral1 biimprd sylsyld ) BCEBFDBEDFZAABFZADFZBCD
      DBGABCHMONAADBMAIJKL $.
      $( [25-May-2011] $) $( [5-Aug-1993] $)

    $( A generalization of axiom ~ ax-16 . $)
    a16gb $p |- ( A. x x = y -> ( ph <-> A. z ph ) ) $=
      ( weq wal a16g ax-4 impbid1 ) BCEBFAADFABCDGADHI $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.
    albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule). $)
    albidv $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( ax-17 albid ) ABCDADFEG $.
      $( [5-Aug-1993] $)

    $( Formula-building rule for existential quantifier (deduction rule). $)
    exbidv $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( ax-17 exbid ) ABCDADFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    2albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 2 existential quantifiers (deduction rule). $)
    2albidv $p |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) ) $=
      ( wal albidv ) ABEGCEGDABCEFHH $.
      $( [4-Mar-1997] $)

    $( Formula-building rule for 2 existential quantifiers (deduction rule). $)
    2exbidv $p |- ( ph -> ( E. x E. y ps <-> E. x E. y ch ) ) $=
      ( wex exbidv ) ABEGCEGDABCEFHH $.
      $( [1-May-1995] $)
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    3exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 3 existential quantifiers (deduction rule). $)
    3exbidv $p |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) ) $=
      ( wex exbidv 2exbidv ) ABFHCFHDEABCFGIJ $.
      $( [1-May-1995] $)
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.  $d w ph $.
    4exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 4 existential quantifiers (deduction rule). $)
    4exbidv $p |- ( ph ->
                     ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) ) $=
      ( wex 2exbidv ) ABGIFICGIFIDEABCFGHJJ $.
      $( [3-Aug-1995] $)
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.9 of [Margaris] p. 89. $)
    19.9v $p |- ( E. x ph <-> ph ) $=
      ( ax-17 19.9 ) ABABCD $.
      $( [21-May-2007] $) $( [28-May-1995] $)
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.21 of [Margaris] p. 90. _Notational
       convention_:  We sometimes suffix with "v" the label of a theorem
       eliminating a hypothesis such as ` ( ph -> A. x ph ) ` in ~ 19.21 via
       the use of distinct variable conditions combined with ~ ax-17 .
       Conversely, we sometimes suffix with "f" the label of a theorem
       introducing such a hypothesis to eliminate the need for the distinct
       variable condition; e.g. ~ euf derived from ~ df-eu .  The "f" stands
       for "not free in" which is less restrictive than "does not occur in." $)
    19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( ax-17 19.21 ) ABCACDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.
    alrimiv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90. $)
    alrimiv $p |- ( ph -> A. x ps ) $=
      ( ax-17 alrimi ) ABCACEDF $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    alrimivv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90. $)
    alrimivv $p |- ( ph -> A. x A. y ps ) $=
      ( wal alrimiv ) ABDFCABDEGG $.
      $( [31-Jul-1995] $)
  $}

  ${
    $d x ph $.  $d x ps $.
    alrimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90. $)
    alrimdv $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( ax-17 alrimd ) ABCDADFBDFEG $.
      $( [10-Feb-1997] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Quantification of two variables over a formula in which they do not
       occur.  (Contributed by Alan Sare, 12-Apr-2011.) $)
    2ax17 $p |- ( ph -> A. x A. y ph ) $=
      ( id alrimivv ) AABCADE $.
      $( [12-Apr-2011] $)
  $}

  ${
    $d x ph $.
    alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90. $)
    alimdv $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( ax-17 alimd ) ABCDADFEG $.
      $( [3-Apr-1994] $)

    $( Deduction from Theorem 19.22 of [Margaris] p. 90. $)
    eximdv $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( ax-17 eximd ) ABCDADFEG $.
      $( [27-Apr-1994] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    2alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90. $)
    2alimdv $p |- ( ph -> ( A. x A. y ps -> A. x A. y ch ) ) $=
      ( wal alimdv ) ABEGCEGDABCEFHH $.
      $( [27-Apr-2004] $)

    $( Deduction from Theorem 19.22 of [Margaris] p. 90. $)
    2eximdv $p |- ( ph -> ( E. x E. y ps -> E. x E. y ch ) ) $=
      ( wex eximdv ) ABEGCEGDABCEFHH $.
      $( [3-Aug-1995] $)
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.23 of [Margaris] p. 90. $)
    19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( ax-17 19.23 ) ABCBCDE $.
      $( [28-Jun-1998] $)
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem 19.23 of [Margaris] p. 90 extended to two variables. $)
    19.23vv $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) ) $=
      ( wi wal wex 19.23v albii bitri ) ABEDFZCFADGZBEZCFLCGBEKMCABDHILBCHJ $.
      $( [10-Aug-2004] $)
  $}

  ${
    $d x ps $.
    exlimiv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.

       This inference, along with our many variants is
       used to implement a metatheorem called "Rule C" that is given in many
       logic textbooks.  See, for example, Rule C in [Mendelson] p. 81, Rule C
       in [Margaris] p. 40, or Rule C in Hirst and Hirst's _A Primer for Logic
       and Proof_ p. 59 (PDF p. 65) at
       ~ http://www.mathsci.appstate.edu/~~jlh/primer/hirst.pdf .

       In informal proofs, the statement "Let C be an element such that..."
       almost always means an implicit application of Rule C.

       In essence, Rule C states that if we can prove that some element ` x `
       exists satisfying a wff, i.e. ` E. x ph ( x ) ` where ` ph ( x ) ` has
       ` x ` free, then we can use ` ph ( ` C ` ) ` as a hypothesis for the
       proof
       where C is a new (ficticious) constant not appearing previously in
       the proof, nor in any axioms used, nor in the theorem to be proved.  The
       purpose of Rule C is to get rid of the existential quantifier.

       We cannot do this in Metamath directly.  Instead, we use the original
       ` ph ` (containing ` x ` ) as an antecedent for the main part of the
       proof.  We eventually arrive at ` ( ph -> ps ) ` where ` ps ` is the
       theorem to be proved and does not contain ` x ` .  Then we apply
       ~ exlimiv to arrive at ` ( E. x ph -> ps ) ` .  Finally, we separately
       prove ` E. x ph ` and detach it with modus ponens ~ ax-mp to arrive at
       the final theorem ` ps ` . $)
    exlimiv $p |- ( E. x ph -> ps ) $=
      ( ax-17 exlimi ) ABCBCEDF $.
      $( [25-Jul-2012] $) $( [5-Aug-1993] $)
  $}

  ${
    $d ph y $.  $d ps x $.
    $( Theorem *11.53 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm11.53 $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $=
      ( wi wal wex 19.21v albii ax-17 hbal 19.23 bitri ) ABEDFZCFABDFZEZCFACGOE
      NPCABDHIAOCBCDBCJKLM $.
      $( [24-May-2011] $)
  $}

  ${
    $d x ps $.  $d y ps $.
    exlimivv.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90. $)
    exlimivv $p |- ( E. x E. y ph -> ps ) $=
      ( wex exlimiv ) ADFBCABDEGG $.
      $( [1-Aug-1995] $)
  $}

  ${
    $d x ch $.  $d x ph $.  $d y ch $.  $d y ph $.
    exlimdvv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90. $)
    exlimdvv $p |- ( ph -> ( E. x E. y ps -> ch ) ) $=
      ( wex exlimdv ) ABEGCDABCEFHH $.
      $( [31-Jul-1995] $)
  $}

  ${
    $d x ps $.
    $( Theorem 19.27 of [Margaris] p. 90. $)
    19.27v $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( ax-17 19.27 ) ABCBCDE $.
      $( [3-Jun-2004] $)
  $}

  ${
    $d x ph $.
    $( Theorem 19.28 of [Margaris] p. 90. $)
    19.28v $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( ax-17 19.28 ) ABCACDE $.
      $( [25-Mar-2004] $)
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.36 of [Margaris] p. 90. $)
    19.36v $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( ax-17 19.36 ) ABCBCDE $.
      $( [18-Aug-1993] $)
  $}

  ${
    $d x ps $.
    19.36aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.36 of [Margaris] p. 90. $)
    19.36aiv $p |- ( A. x ph -> ps ) $=
      ( ax-17 19.36i ) ABCBCEDF $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.  $d y ph $.
    $( Special case of ~ 19.12 where its converse holds.  (Unnecessary distinct
       variable restrictions were removed by Andrew Salmon, 11-Jul-2011.) $)
    19.12vv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      ( wal wex 19.21v exbii ax-17 hbal 19.36 19.36v albii 19.21 bitr2i 3bitri
      wi ) ABQZDEZCFABDEZQZCFACEZTQZRCFZDEZSUACABDGHATCBCDBCIJKUEUBBQZDEUCUDUFD
      ABCLMUBBDADCADIJNOP $.
      $( [11-Jul-2011] $) $( [18-Jul-2001] $)
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.37 of [Margaris] p. 90. $)
    19.37v $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( ax-17 19.37 ) ABCACDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ph $.
    19.37aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.37 of [Margaris] p. 90. $)
    19.37aiv $p |- ( ph -> E. x ps ) $=
      ( wi wex 19.37v mpbi ) ABECFABCFEDABCGH $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.41 of [Margaris] p. 90. $)
    19.41v $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( ax-17 19.41 ) ABCBCDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 2 quantifiers. $)
    19.41vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x E. y ph /\ ps ) ) $=
      ( wa wex 19.41v exbii bitri ) ABEDFZCFADFZBEZCFKCFBEJLCABDGHKBCGI $.
      $( [30-Apr-1995] $)
  $}

  ${
    $d x ps $.  $d y ps $.  $d z ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 3 quantifiers. $)
    19.41vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                     ( E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vv exbii 19.41v bitri ) ABFEGDGZCGAEGDGZBFZCGMCGBFLNCABDEHI
      MBCJK $.
      $( [30-Apr-1995] $)
  $}

  ${
    $d w ps $.  $d x ps $.  $d y ps $.  $d z ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 4 quantifiers.  (Contributed by
       FL, 14-Jul-2007.) $)
    19.41vvvv $p |- ( E. w E. x E. y E. z ( ph /\ ps ) <->
                     ( E. w E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vvv exbii 19.41v bitri ) ABGEHDHCHZFHAEHDHCHZBGZFHNFHBGMOFA
      BCDEIJNBFKL $.
      $( [14-Jul-2007] $)
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.42 of [Margaris] p. 90. $)
    19.42v $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( ax-17 19.42 ) ABCACDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d y ph $.
    $( Distribution of existential quantifiers. $)
    exdistr $p |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) ) $=
      ( wa wex 19.42v exbii ) ABEDFABDFECABDGH $.
      $( [9-Mar-1995] $)
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Theorem 19.42 of [Margaris] p. 90 with 2 quantifiers. $)
    19.42vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( ph /\ E. x E. y ps ) ) $=
      ( wa wex exdistr 19.42v bitri ) ABEDFCFABDFZECFAJCFEABCDGAJCHI $.
      $( [16-Mar-1995] $)
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    $( Theorem 19.42 of [Margaris] p. 90 with 3 quantifiers. $)
    19.42vvv $p |- ( E. x E. y E. z ( ph /\ ps )
                       <-> ( ph /\ E. x E. y E. z ps ) ) $=
      ( wa wex 19.42vv exbii 19.42v bitri ) ABFEGDGZCGABEGDGZFZCGAMCGFLNCABDEHI
      AMCJK $.
      $( [21-Sep-2011] $)
  $}

  ${
    $d y ph $.  $d z ph $.
    $( Distribution of existential quantifiers. $)
    exdistr2 $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                   E. x ( ph /\ E. y E. z ps ) ) $=
      ( wa wex 19.42vv exbii ) ABFEGDGABEGDGFCABDEHI $.
      $( [17-Mar-1995] $)
  $}

  ${
    $d y ph $.  $d z ph $.  $d z ps $.
    $( Distribution of existential quantifiers.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3exdistr $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ch ) ) ) $=
      ( w3a wex wa 3anass 2exbii 19.42vv exdistr anbi2i 3bitri exbii ) ABCGZFHE
      HZABCFHIEHZIZDRABCIZIZFHEHAUAFHEHZITQUBEFABCJKAUAEFLUCSABCEFMNOP $.
      $( [25-May-2011] $) $( [9-Mar-1995] $)
  $}

  ${
    $d y ph $.  $d z ph $.  $d w ph $.  $d z ps $.  $d w ps $.  $d w ch $.
    $( Distribution of existential quantifiers. $)
    4exdistr $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $=
      ( wa wex anass exbii 19.42v anbi2i 3bitri bitri ) ABICDIZIZHJZGJZFJZABCDH
      JIZGJIZFJIZEUAAUCIZFJUDTUEFTABUBIZIZGJAUFGJZIUESUGGSABQIZIZHJZUGRUJHABQKL
      UKAUIHJZIABQHJZIZIUGAUIHMULUNABQHMNUNUFAUMUBBCDHMNNOPLAUFGMUHUCABUBGMNOLA
      UCFMPL $.
      $( [9-Mar-1995] $)
  $}

  ${
    $d y ph $.  $d x ps $.
    cbvalv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbvalv $p |- ( A. x ph <-> A. y ps ) $=
      ( ax-17 cbval ) ABCDADFBCFEG $.
      $( [5-Aug-1993] $)

    $( Rule used to change bound variables, using implicit substitition. $)
    cbvexv $p |- ( E. x ph <-> E. y ps ) $=
      ( ax-17 cbvex ) ABCDADFBCFEG $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d y x $.  $d y z $.  $d w x $.  $d w z $.
    cbval2.1 $e |- ( ph -> A. z ph ) $.
    cbval2.2 $e |- ( ph -> A. w ph ) $.
    cbval2.3 $e |- ( ps -> A. x ps ) $.
    cbval2.4 $e |- ( ps -> A. y ps ) $.
    cbval2.5 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbval2 $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal hbal weq wb wa ax-17 hban cbval 19.28v expcom pm5.32d 3bitr3i mpbir
      wi pm5.32 ) ADLZBFLZCEAEDGMBCFIMCENZUGUHOUEUIUGPZUIUHPZOUIAPZDLUIBPZFLUJU
      KULUMDFUIAFUIFQHRUIBDUIDQJRDFNZUIABUIUNABOKUAUBSUIADTUIBFTUCUIUGUHUFUDS
      $.
      $( [22-Dec-2003] $)

    $( Rule used to change bound variables, using implicit substitition. $)
    cbvex2 $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wex hbex weq wb wa ax-17 hban cbvex 19.42v expcom pm5.32d 3bitr3i mpbir
      wi pm5.32 ) ADLZBFLZCEAEDGMBCFIMCENZUGUHOUEUIUGPZUIUHPZOUIAPZDLUIBPZFLUJU
      KULUMDFUIAFUIFQHRUIBDUIDQJRDFNZUIABUIUNABOKUAUBSUIADTUIBFTUCUIUGUHUFUDS
      $.
      $( [14-Sep-2003] $)
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x w $.  $d z y $.
    cbval2v.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbval2v $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( ax-17 cbval2 ) ABCDEFAEHAFHBCHBDHGI $.
      $( [4-Feb-2005] $)

    $( Rule used to change bound variables, using implicit substitition. $)
    cbvex2v $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( ax-17 cbvex2 ) ABCDEFAEHAFHBCHBDHGI $.
      $( [26-Jul-1995] $)
  $}

  ${
    $d x ph $.  $d x ch $.
    cbvald.1 $e |- ( ph -> A. y ph ) $.
    cbvald.2 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbvald.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables, using implicit substitition,
       particularly useful in conjunction with ~ dvelim .  (The proof was
       shortened by Andrew Salmon, 25-May-2011.) $)
    cbvald $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal wb ax-17 hbal a17d cbv2 3syl ) AAEIZPDIBDICEIJFADEADKLABCDEGACDMHNO
      $.
      $( [25-May-2011] $) $( [2-Jan-2002] $)

    $( Deduction used to change bound variables, using implicit substitition,
       particularly useful in conjunction with ~ dvelim . $)
    cbvexd $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wn wal wex hbnd weq wb notbi syl6ib cbvald notbid df-ex 3bitr4g ) ABIZD
      JZICIZEJZIBDKCEKAUBUDAUAUCDEFABEFGLADEMBCNUAUCNHBCOPQRBDSCEST $.
      $( [2-Jan-2002] $)
  $}

  ${
    $v f $.
    $v g $.
    $( Define temporary individual variables. $)
    cbvex4v.vf $f set f $.
    cbvex4v.vg $f set g $.
    $d w z ch $.  $d u v ph $.  $d x y ps $.  $d f g ps $.  $d f w $.
    $d g z $.  $d u v w x y z $.
    cbvex4v.1 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
    cbvex4v.2 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
    $( Rule used to change bound variables, using implicit substitition. $)
    cbvex4v $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $=
      ( wex weq wa 2exbidv cbvex2v 2exbii bitri ) AGNFNZENDNBGNFNZINHNCKNJNZINH
      NUAUBDEHIDHOEIOPABFGLQRUBUCHIBCFGJKMRST $.
      $( [26-Jul-1995] $)
  $}

  ${
    eean.1 $e |- ( ph -> A. y ph ) $.
    eean.2 $e |- ( ps -> A. x ps ) $.
    $( Rearrange existential quantifiers. $)
    eean $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( wa wex 19.42 exbii hbex 19.41 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
      $( [27-Oct-2010] $)
  $}

  ${
    $d y ph $.  $d x ps $.
    $( Rearrange existential quantifiers. $)
    eeanv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( ax-17 eean ) ABCDADEBCEF $.
      $( [26-Jul-1995] $)
  $}

  ${
    $d y ph $.  $d z ph $.  $d x z ps $.  $d x y ch $.
    $( Rearrange existential quantifiers.  (The proof was shortened by Andrew
       Salmon, 25-May-2011.) $)
    eeeanv $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                 ( E. x ph /\ E. y ps /\ E. z ch ) ) $=
      ( w3a wex wa df-3an 3exbii eeanv exbii anbi1i 19.41v 3bitr4i 3bitri ) ABC
      GZFHEHDHABIZCIZFHEHZDHSEHZCFHZIZDHZADHZBEHZUCGZRTDEFABCJKUAUDDSCEFLMUBDHZ
      UCIUFUGIZUCIUEUHUIUJUCABDELNUBUCDOUFUGUCJPQ $.
      $( [25-May-2011] $) $( [26-Jul-1995] $)
  $}

  ${
    $d z ph $.  $d w ph $.  $d x ps $.  $d y ps $.  $d y z $.  $d w x $.
    $( Rearrange existential quantifiers. $)
    ee4anv $p |- ( E. x E. y E. z E. w ( ph /\ ps ) <->
                  ( E. x E. y ph /\ E. z E. w ps ) ) $=
      ( wa wex excom exbii eeanv 2exbii 3bitri ) ABGFHZEHDHZCHNDHZEHZCHADHZBFHZ
      GZEHCHRCHSEHGOQCNDEIJPTCEABDFKLRSCEKM $.
      $( [31-Jul-1995] $)
  $}

  ${
    $d x ph $.
    nexdv.1 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff. $)
    nexdv $p |- ( ph -> -. E. x ps ) $=
      ( ax-17 nexd ) ABCACEDF $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x ps $.
    chv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem. $)
    chvarv $p |- ps $=
      ( a4v mpg ) ABCABCDEGFH $.
      $( [20-Apr-1994] $)
  $}

  ${
    $d x z $.  $d y z $.
    $( When the class variables of set theory are replaced with set
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the set variables in ~ wel with the class
       variables in ~ wcel . $)
    cleljust $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      ( weq wel wa wex ax-17 elequ1 equsex bicomi ) CADCBEZFCGABEZLMCAMCHCABIJK
      $.
      $( [28-Jan-2004] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        More substitution theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( The theorems in this section make use of the $d statement. $)

  ${
    $d y z $.  $d x y $.
    $( Lemma for ~ equsb3 .  (The proof was shortened by Andrew Salmon,
       14-Jun-2011.) $)
    equsb3lem $p |- ( [ x / y ] y = z <-> x = z ) $=
      ( cv wceq ax-17 equequ1 sbie ) BDCDZEADIEZBAJBFBACGH $.
      $( [14-Jun-2011] $) $( [4-Dec-2005] $)
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic wff.  (Contributed by Raph Levien and
       FL, 4-Dec-2005.) $)
    equsb3 $p |- ( [ x / y ] y = z <-> x = z ) $=
      ( vw weq wsb equsb3lem sbbii ax-17 sbco2 3bitr3i ) BCEZBDFZDAFDCEZDAFLBAF
      ACEMNDADBCGHLBADLDIJADCGK $.
      $( [4-Dec-2005] $)
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (The proof was
       shortened by Andrew Salmon, 14-Jun-2011.) $)
    elsb3 $p |- ( [ x / y ] y e. z <-> x e. z ) $=
      ( vw wel wsb ax-17 elequ1 sbie sbbii sbco2 bitr3i wb weq sbimi ax-mp sbbi
      equsb1 mpbi sbf 3bitri ) BCEZBAFZDCEZDAFZACEZDAFZUFUCUDDBFZBAFUEUHUBBAUDU
      BDBUBDGDBCHIJUDDABUDBGKLUDUFMZDAFZUEUGMDANZDAFUJDARUKUIDADACHOPUDUFDAQSUF
      DAUFDGTUA $.
      $( [14-Jun-2011] $) $( [7-Nov-2006] $)
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (Contributed by
       Rodolfo Medina, 3-Apr-2010.)  (The proof was shortened by Andrew Salmon,
       14-Jun-2011.) $)
    elsb4 $p |- ( [ x / y ] z e. y <-> z e. x ) $=
      ( vw wel wsb ax-17 elequ2 sbie sbbii sbco2 bitr3i wb weq sbimi ax-mp sbbi
      equsb1 mpbi sbf 3bitri ) CBEZBAFZCDEZDAFZCAEZDAFZUFUCUDDBFZBAFUEUHUBBAUDU
      BDBUBDGDBCHIJUDDABUDBGKLUDUFMZDAFZUEUGMDANZDAFUJDARUKUIDADACHOPUDUFDAQSUF
      DAUFDGTUA $.
      $( [14-Jun-2011] $) $( [3-Apr-2010] $)
  $}

  ${
    $d x y $.
    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct. $)
    hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( weq wal wsb wi ax-16 hbsb2 pm2.61i ) BCDBEABCFZKBEGKBCHABCIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d y ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ." $)
    sbhb $p |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) $=
      ( wal wi wsb ax-17 sb8 imbi2i 19.21v bitr4i ) AABDZEAABCFZCDZEAMECDLNAABC
      ACGHIAMCJK $.
      $( [29-May-2009] $)
  $}

  ${
    $d x y z $.  $d y z ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by G&eacute;rard Lang, 14-Nov-2013.) $)
    sbhb2 $p |- ( A. x ( ph -> A. x ph )
           <-> A. y A. z ( [ y / x ] ph <-> [ z / x ] ph ) ) $=
      ( cv wsbc wb wal wi 2albiim sbhb albii alcom bitri ax-17 sb8 sblim 3bitri
      wa hbs1 anbi12i anidm 3bitr2ri ) ABCEZFZABDEZFZGDHCHUEUGIZDHCHZUGUEIZDHZC
      HZSAABHIZBHZUNSUNUEUGCDJUNUIUNULUNAUGIZBHZDHZUHCHZDHUIUNUODHZBHUQUMUSBABD
      KLUOBDMNUPURDUPUOBUDFZCHURUOBCUOCOPUTUHCAUGBCABDTQLNLUHDCMRUNAUEIZCHZBHVA
      BHZCHULUMVBBABCKLVABCMVCUKCVCVABUFFZDHUKVABDVADOPVDUJDAUEBDABCTQLNLRUAUNU
      BUC $.
      $( [14-Nov-2013] $)
  $}

  ${
    $d y z $.
    hbsb.1 $e |- ( ph -> A. z ph ) $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct. $)
    hbsb $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $=
      ( weq wal wsb wi ax-16 hbsb4 pm2.61i ) DCFDGABCHZMDGIMDCJABCDEKL $.
      $( [12-Aug-1993] $)
  $}

  ${
    $d y z $.
    hbsbd.1 $e |- ( ph -> A. x ph ) $.
    hbsbd.2 $e |- ( ph -> A. z ph ) $.
    hbsbd.3 $e |- ( ph -> ( ps -> A. z ps ) ) $.
    $( Deduction version of ~ hbsb . $)
    hbsbd $p |- ( ph -> ( [ y / x ] ps -> A. z [ y / x ] ps ) ) $=
      ( cv wceq wal wsbc wi wn alrimi 2alimi hbsb4t 3syl ax-16 pm2.61d2 ) AEIDI
      ZJEKZBCUALZUCEKMZAAEKZCKBBEKMZEKCKUBNUDMAUECFGOAUFCEHPBCDEQRUCEDST $.
      $( [15-Feb-2013] $)
  $}

  ${
    $d x y z $.  $d w y $.
    $( Equivalence for double substitution. $)
    2sb5 $p |- ( [ z / x ] [ w / y ] ph <->
               E. x E. y ( ( x = z /\ y = w ) /\ ph ) ) $=
      ( wsb weq wa wex sb5 19.42v anass exbii anbi2i 3bitr4ri bitri ) ACEFZBDFB
      DGZQHZBIRCEGZHAHZCIZBIQBDJSUBBRTAHZHZCIRUCCIZHUBSRUCCKUAUDCRTALMQUERACEJN
      OMP $.
      $( [3-Feb-2005] $)

    $( Equivalence for double substitution. $)
    2sb6 $p |- ( [ z / x ] [ w / y ] ph <->
               A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wsb weq wi wal wa sb6 19.21v impexp albii imbi2i 3bitr4ri bitri ) ACEFZ
      BDFBDGZRHZBISCEGZJAHZCIZBIRBDKTUCBSUAAHZHZCISUDCIZHUCTSUDCLUBUECSUAAMNRUF
      SACEKOPNQ $.
      $( [3-Feb-2005] $)
  $}

  ${
    $d x z $.  $d x w $.  $d y z $.
    $( Commutativity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint). $)
    sbcom2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( weq wal wsb wb wn wi albii 19.21v sb4b imbi2d albidv hbae sbequ12 sbbid
      a4s wa alcom bi2.04 bitri 3bitr3i a1i sylan9bbr sylan9bb 3bitr4d pm2.61ii
      ex bitr3d ) BCFZBGZDEFZDGZABCHZDEHZADEHZBCHZIZUNJZUPJZVAVBVCUAZUOUMAKZBGZ
      KZDGZUMUOAKZDGZKZBGZURUTVHVLIVDUMVIKZBGZDGVMDGZBGVHVLVMDBUBVNVGDVNUOVEKZB
      GVGVMVPBUMUOAUCLUOVEBMUDLVOVKBUMVIDMLUEUFVCURUOUQKZDGVBVHUQDENVBVQVGDVBUQ
      VFUOABCNOPUGVBUTUMUSKZBGVCVLUSBCNVCVRVKBVCUSVJUMADENOPUHUIUKUNUSURUTUNAUQ
      DEBCDQUMAUQIBABCRTSUMUSUTIBUSBCRTULUPUQURUTUOUQURIDUQDERTUPAUSBCDEBQUOAUS
      IDADERTSULUJ $.
      $( [27-May-1997] $)
  $}

  ${
    $d ph x y z $.  $d w x z $.
    $( Theorem *11.07 in [WhiteheadRussell] p. 159.  (Contributed by Andrew
       Salmon, 17-Jun-2011.) $)
    pm11.07 $p |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( cv wceq wa wex wsbc a9e pm3.2i 2th eeanv 3bitr4i anbi1i 19.41vv 2sb5 )
      BFZEFZGZDFZCFZGZHZAHDIBIZSUCGZUBTGZHZAHDIBIZADUCJBTJADTJBUCJUEDIBIZAHUIDI
      BIZAHUFUJUKULAUABIZUDDIZHZUGBIZUHDIZHZUKULUOURUMUNBEKDCKLUPUQBCKDEKLMUAUD
      BDNUGUHBDNOPUEABDQUIABDQOABDECRABDCERO $.
      $( [17-Jun-2011] $)
  $}

  ${
    $d x y $.
    $( Equivalence for substitution. $)
    sb6a $p |- ( [ y / x ] ph <-> A. x ( x = y -> [ x / y ] ph ) ) $=
      ( wsb weq wi wal sb6 wb sbequ12 equcoms pm5.74i albii bitri ) ABCDBCEZAFZ
      BGOACBDZFZBGABCHPRBOAQAQICBACBJKLMN $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.  $d x w $.  $d y z $.  $d z w $.
    2sb5rf.1 $e |- ( ph -> A. z ph ) $.
    2sb5rf.2 $e |- ( ph -> A. w ph ) $.
    $( Reversed double substitution. $)
    2sb5rf $p |- ( ph <->
                E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) ) $=
      ( weq wsb wex sb5rf 19.42v sbcom2 anbi2i anass bitri exbii hbsb 3bitr4ri
      wa ) ADBHZABDIZTZDJUAECHZTZACEIBDIZTZEJZDJABDFKUCUHDUAUDUBCEIZTZTZEJUAUJE
      JZTUHUCUAUJELUGUKEUGUEUITUKUFUIUEACEBDMNUAUDUIOPQUBULUAUBCEABDEGRKNSQP $.
      $( [3-Feb-2005] $)

    $( Reversed double substitution. $)
    2sb6rf $p |- ( ph <->
                A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) ) $=
      ( weq wsb wi wal wa sb6rf 19.21v sbcom2 imbi2i impexp bitri albii hbsb
      3bitr4ri ) ADBHZABDIZJZDKUBECHZLZACEIBDIZJZEKZDKABDFMUDUIDUBUEUCCEIZJZJZE
      KUBUKEKZJUIUDUBUKENUHULEUHUFUJJULUGUJUFACEBDOPUBUEUJQRSUCUMUBUCCEABDEGTMP
      UASR $.
      $( [3-Feb-2005] $)
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( An alternate definition of proper substitution ~ df-sb .  By introducing
       a dummy variable ` z ` in the definiens, we are able to eliminate any
       distinct variable restrictions among the variables ` x ` , ` y ` , and
       ` ph ` of the definiendum.  No distinct variable conflicts arise because
       ` z ` effectively insulates ` x ` from ` y ` .  To achieve this, we use
       a chain of two substitutions in the form of ~ sb5 , first ` z ` for
       ` x ` then ` y ` for ` z ` .  Compare Definition 2.1'' of [Quine] p. 17.
       Theorem
       ~ sb7f provides a version where ` ph ` and ` z ` don't have to be
       distinct. $)
    dfsb7 $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( wsb weq wa wex sb5 sbbii ax-17 sbco2 3bitr3i ) ABDEZDCEBDFAGBHZDCEABCED
      CFOGDHNODCABDIJABCDADKLODCIM $.
      $( [28-Jan-2004] $)
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    sb7f.1 $e |- ( ph -> A. z ph ) $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (The proof was shortened by Andrew
       Salmon, 25-May-2011.) $)
    sb7f $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( wsb weq wa wex sb5 sbbii sbco2 3bitr3i ) ABDFZDCFBDGAHBIZDCFABCFDCGOHDI
      NODCABDJKABCDELODCJM $.
      $( [25-May-2011] $) $( [26-Jul-2006] $)
  $}

  ${
    $d x y $.
    sb10f.1 $e |- ( ph -> A. x ph ) $.
    $( Hao Wang's identity axiom P6 in Irving Copi, _Symbolic Logic_ (5th ed.,
       1979), p. 328.  In traditional predicate calculus, this is a sole axiom
       for identity from which the usual ones can be derived. $)
    sb10f $p |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) ) $=
      ( weq wsb wa wex hbsb sbequ equsex bicomi ) BCFADBGZHBIADCGZNOBCADCBEJABC
      DKLM $.
      $( [9-May-2005] $)
  $}

  ${
    $d x ph $.
    $( An identity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint). $)
    sbid2v $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( ax-17 sbid2 ) ABCABDE $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.  $d x ph $.
    $( Elimination of substitution. $)
    sbelx $p |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) ) $=
      ( wsb weq wa wex sbid2v sb5 bitr3i ) AACBDZBCDBCEKFBGABCHKBCIJ $.
      $( [5-Aug-1993] $)
  $}

  ${
    $( Note:  A more general case could also be proved with
       "$d x z $.  $d y w $.  $d x ph $.  $d y ph $.", but with more
       difficulty. $)
    $d x y z $.  $d w y $.  $d x y ph $.
    $( Elimination of double substitution. $)
    sbel2x $p |- ( ph <-> E. x E. y ( ( x = z /\ y = w ) /\
                     [ y / w ] [ x / z ] ph ) ) $=
      ( weq wsb wa wex sbelx anbi2i exbii exdistr 3bitr4i anass 2exbii bitr4i )
      ABDFZCEFZADBGZECGZHZHZCIBIZRSHUAHZCIBIRTHZBIRUBCIZHZBIAUDUFUHBTUGRTCEJKLA
      BDJRUBBCMNUEUCBCRSUAOPQ $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.
    $( A theorem used in elimination of disjoint variable restriction on ` x `
       and ` y ` by replacing it with a distinctor ` -. A. x x = z ` . $)
    sbal1 $p |- ( -. A. x x = z ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wb wi sbequ12 a4s dral2 bitr3d a1d wa hba1 al2imi hbnaes
      syl6 hbsb4 ax-4 sbimi alimi adantl sb4 ax-7 dveeq2 alim sb2 sylan9 impbid
      syl9 ex pm2.61i ) CDEZCFZBDEBFGZABFZCDHZACDHZBFZIZJUQVCURUQUSUTVBUPUSUTIC
      USCDKLAVACDBUPAVAICACDKLMNOUQGZURVCVDURPUTVBURUTVBJVDURUTUTBFVBUSCDBABQUA
      UTVABUSACDABUBUCUDTUEVDVBUPAJZBFZCFZURUTVDVBVECFZBFZVGVBVIJCDBVDVAVHBACDU
      FRSVEBCUGTVGUTJBDCURCFVGUPUSJZCFUTURVFVJCURUPUPBFVFUSBDCUHUPABUIUMRUSCDUJ
      TSUKULUNUO $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.  $d x z $.
    $( Move universal quantifier in and out of substitution. $)
    sbal $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $=
      ( weq wal wsb wb a16gb sbimi sbequ5 sbbi 3imtr3i bitr3d sbal1 pm2.61i ) B
      DEBFZABFZCDGZACDGZBFZHQTSUAQCDGARHZCDGQTSHQUBCDABDBIJBDCDKARCDLMTBDBINABC
      DOP $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d x y $.  $d x z $.
    $( Move existential quantifier in and out of substitution. $)
    sbex $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $=
      ( wn wal wsb wex sbn sbal albii bitri xchbinx df-ex sbbii 3bitr4i ) AEZBF
      ZEZCDGZACDGZEZBFZEABHZCDGUABHTRCDGZUCRCDIUEQCDGZBFUCQBCDJUFUBBACDIKLMUDSC
      DABNOUABNP $.
      $( [27-Sep-2003] $)
  $}

  ${
    $d x z $.  $d y z $.
    sbalv.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Quantify with new variable inside substitution. $)
    sbalv $p |- ( [ y / x ] A. z ph <-> A. z ps ) $=
      ( wal wsb sbal albii bitri ) AEGCDHACDHZEGBEGAECDILBEFJK $.
      $( [18-Aug-1993] $)
  $}

  ${
    $d x y $.  $d y ph $.
    $( An equivalent expression for existence. $)
    exsb $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $=
      ( wex wsb weq wi wal ax-17 sb8e sb6 exbii bitri ) ABDABCEZCDBCFAGBHZCDABC
      ACIJNOCABCKLM $.
      $( [2-Feb-2005] $)
  $}

  ${
    $d x y z $.  $d y w $.  $d z w ph $.
    $( An equivalent expression for double existence. $)
    2exsb $p |- ( E. x E. y ph <->
                  E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wex weq wi wal exsb exbii excom bitri impexp albii 19.21v bitr2i 3bitri
      wa ) ACFZBFZCEGZAHZCIZBFZEFZBDGZUBSAHZCIZBIZDFZEFUJEFDFUAUDEFZBFUFTULBACE
      JKUDBELMUEUKEUEUGUDHZBIZDFUKUDBDJUNUJDUMUIBUIUGUCHZCIUMUHUOCUGUBANOUGUCCP
      QOKMKUJEDLR $.
      $( [2-Feb-2005] $)
  $}

  ${
    $d z ps $.
    dvelim.1 $e |- ( ph -> A. x ph ) $.
    dvelim.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( This theorem can be used to eliminate a distinct variable restriction on
       ` x ` and ` z ` and replace it with the "distinctor" ` -. A. x x = y `
       as an antecedent. ` ph ` normally has ` z ` free and can be read
       ` ph ( z ) ` , and ` ps ` substitutes ` y ` for ` z ` and can be read
       ` ph ( y ) ` .  We don't require that ` x ` and ` y ` be distinct: if
       they aren't, the distinctor will become false (in multiple-element
       domains of discourse) and "protect" the consequent.

       To obtain a closed-theorem form of this inference, prefix the hypotheses
       with ` A. x A. z ` , conjoin them, and apply ~ dvelimdf .

       Other variants of this theorem are ~ dvelimf (with no distinct variable
       restrictions), ~ dvelimfALT (that avoids ~ ax-11 ), and ~ dvelimALT
       (that avoids ~ ax-10 ). $)
    dvelim $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( ax-17 dvelimf ) ABCDEFBEHGI $.
      $( [23-Nov-1994] $)
  $}

  ${
    $d z ps $.  $d x z $.  $d y z $.
    dvelimALT.1 $e |- ( ph -> A. x ph ) $.
    dvelimALT.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim that doesn't use ~ ax-10 .  (See ~ dvelimfALT for a
       version that doesn't use ~ ax-11 .) $)
    dvelimALT $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi ax-17 hba1 ax16ALT a1i hbimd a1d wa hbn hban ax-12 imp ex
      pm2.61i hbald equsal albii 3imtr3g ) CDHZCIZJZEDHZAKZEIZUNCIBBCIUKUMCEUKE
      LCEHZCIZUKUMUMCIKZKUPUQUKUPULACUOCMZULCENAACIKZUPFOPQUPJZUKUQUTUKRZULACUT
      UKCUPCURSUJCUICMSTUTUKULULCIKEDCUAUBUSVAFOPUCUDUEABEDBELGUFZUNBCVBUGUH $.
      $( [17-May-2008] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct. $)
    dveeq1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq ax-17 equequ1 dvelim ) DCEZBCEABDIAFDBCGH $.
      $( [2-Jan-2002] $)

    $( Version of ~ dveeq1 using ~ ax-16 instead of ~ ax-17 . $)
    dveeq1ALT $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq ax17eq equequ1 dvelimfALT ) DCEBCEABDDCAFBCDFDBCGH $.
      $( [29-Apr-2008] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct. $)
    dveel1 $p |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) ) $=
      ( vw wel ax-17 elequ1 dvelimfALT ) DCEZBCEZABDIAFJDFDBCGH $.
      $( [2-Jan-2002] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct. $)
    dveel2 $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel ax-17 elequ2 dvelimfALT ) CDEZCBEZABDIAFJDFDBCGH $.
      $( [2-Jan-2002] $)
  $}

  ${
    $d z y $.  $d z x $.
    $( Move quantifier in and out of substitution. $)
    sbal2 $p |- ( -. A. x x = y ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wi wsb alcom hbnae dveeq1 alimi hbnaes 19.21t albid syl5rbbr
      wb syl sb6 albii 3bitr4g ) BCEBFGZCDEZABFZHZCFZUDAHZCFZBFZUECDIACDIZBFUJU
      HBFZCFUCUGUHCBJUCULUFCBCCKUCUDUDBFHZBFZULUFRUNBCBUCUMBBCDLMNUDABOSPQUECDT
      UKUIBACDTUAUB $.
      $( [2-Jan-2002] $)
  $}

  ${
    $d w y $.  $d w z $.  $d w x $.  $( ` w ` is dummy. $)
    $( Axiom ~ ax-15 is redundant if we assume ~ ax-17 .  Remark 9.6 in
       [Megill] p. 448 (p. 16 of the preprint), regarding axiom scheme C14'.

       Note that ` w ` is a dummy variable introduced in the proof.  On the web
       page, it is implicitly assumed to be distinct from all other variables.
       (This is made explicit in the database file set.mm).  Its purpose is to
       satisfy the distinct variable requirements of ~ dveel2 and ~ ax-17 .  By
       the end of the proof it has vanished, and the final theorem has no
       distinct variable requirements.

       This theorem should not be referenced in any proof.  Instead, use
       ~ ax-15 below so that theorems needing ~ ax-15 can be more easily
       identified. $)
    ax15 $p |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $=
      ( vw weq wal wn wi hbn1 dveel2 hbim1 ax-17 elequ1 imbi2d dvelimfALT 19.21
      wel syl6ib pm2.86d ) CAECFGZCBEZCFGZABQZUCCFZTUBUCHZUECFUBUDHUBDBQZHUECAD
      UBUFCUACIZCBDJKUEDLDAEUFUCUBDABMNOUBUCCUGPRS $.
      $( [29-Jun-1995] $)
  $}

  $( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms for a non-logical predicate in our predicate calculus with
     equality.  Axiom scheme C14' in [Megill] p. 448 (p. 16 of the preprint).
     It is redundant if we include ~ ax-17 ; see theorem ~ ax15 .  Alternately,
     ~ ax-17 becomes unnecessary in principle with this axiom, but we lose the
     more powerful metalogic afforded by ~ ax-17 .  We retain ~ ax-15 here to
     provide completeness for systems with the simpler metalogic that results
     from omitting ~ ax-17 , which might be easier to study for some
     theoretical purposes. $)
  ax-15 $a |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $.

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.) $)
    ax17el $p |- ( x e. y -> A. z x e. y ) $=
      ( weq wal wel wi ax-15 ax-16 pm2.61ii ) CADCECBDCEABFZKCEGABCHKCAIKCBIJ
      $.
      $( [5-Aug-1993] $)
  $}

  ${
    $d w z x $.  $d w y $.
    $( Version of ~ dveel2 using ~ ax-16 instead of ~ ax-17 . $)
    dveel2ALT $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel ax17el elequ2 dvelimfALT ) CDECBEABDCDAFCBDFDBCGH $.
      $( [10-May-2008] $)
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for equality predicate. $)
    ax11eq $p |- ( -. A. x x = y ->
               ( x = y -> ( z = w -> A. x ( x = y -> z = w ) ) ) ) $=
      ( vu vv weq wal wn wi wa 19.26 a1i wb equequ1 equequ2 a4s imbi2d imbi12d
      exp32 equid ax-gen sylan9bb hba1 albid adantr mpbii sylbir ad2antll ax-12
      impcom adantrr equtrr alimi syl6 sylbid dral2 ad2antrr mpbid imp biimprcd
      adantll adantlr ad2antlr wex a9e ax-1 alrimiv adantl im2anan9 syl exlimdv
      dveeq2 sylibr mpi a1d 4cases ) ACGZAHZADGZAHZABGZAHIZWBCDGZWBWDJZAHZJZJZJ
      ZVSWAKVRVTKZAHZWIVRVTALWKWCWBWGWKWCWBKZKAAGZWBWMJZAHZJZWGWOWMWNAWMWBAUAMU
      BMWKWPWGNWLWKWMWDWOWFWJWMWDNAVRWMCAGZVTWDACAOADCPZUCQZWKWNWEAWJAUDWKWMWDW
      BWSRUESUFUGTUHVSWAIZKZWCWBWGXAWLKVTWBVTJZAHZJZWGWTWLXDVSWTWLKZVTBDGZXCWBV
      TXFNWTWCABDOUIXEXFXFAHZXCWTWCXFXGJZWBWCWTXHBDAUJUKULXFXBABDAUMUNUOUPVBVSX
      DWGNWTWLVSVTWDXCWFVRVTWDNAACDOQZXBWEACAVSVTWDWBXIRUQSURUSTVSIZWAKZWCWBWGX
      KWLKWQWBWQJZAHZJZWGXJWLXNWAXJWLKZWQCBGZXMWBWQXPNXJWCABCPZUIXOXPXPAHZXMXJW
      CXPXRJZWBXJWCXSCBAUJUTULXPXLAWBWQXPXQVAUNUOUPVCWAXNWGNXJWLWAWQWDXMWFVTWQW
      DNAWRQZXLWEADAWAWQWDWBXTRUQSVDUSTXJWTKZWHWCYAWGWBYAEDGZEVEWGEDVFYAYBWGEYA
      FCGZFVEYBWGJZFCVFYAYCYDFYAYCYBWGYAYCYBKZKZFEGZWBYGJZAHZJWGYGYHAYGWBVGVHYF
      YGWDYIWFYEYGWDNZYAYCYGCEGYBWDFCEOEDCPUCZVIYFYEAHZYIWFNYFYCAHZYBAHZKZYLYAY
      EYOXJYCYMWTYBYNACFVMADEVMVJUTYCYBALVNYLYHWEAYEAUDYLYGWDWBYEYJAYKQRUEVKSUG
      TVLVOVLVOVPVPVQ $.
      $( [22-Jan-2007] $)
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for membership predicate. $)
    ax11el $p |- ( -. A. x x = y ->
               ( x = y -> ( z e. w -> A. x ( x = y -> z e. w ) ) ) ) $=
      ( vv vu weq wal wn wel wi wa wb elequ1 elequ2 adantl imbi2d imbi12d exp32
      a4s 19.26 bitrd ax-17 dvelimfALT biimprcd alimi syl6 adantr sylan9bb hba1
      sylbid albid mpbid sylbir ad2antll ax-15 impcom adantrr adantll dral2 imp
      ad2antrr adantlr ad2antlr wex a9e ax-1 alrimiv dveeq2 im2anan9 sylibr syl
      mpbii exlimdv mpi a1d 4cases ) ACGZAHZADGZAHZABGZAHIZWBCDJZWBWDKZAHZKZKZK
      ZVSWALVRVTLZAHZWIVRVTAUAWKWCWBWGWKWCWBLZLAAJZWBWMKZAHZKZWGWLWPWKWLWMBBJZW
      OWBWMWQMWCWBWMBAJWQABANABBOUBZPWCWQWOKWBWCWQWQAHWOEEJZWQABEWSAUCWQEUCEBGW
      SBEJWQEBENEBBOUBUDWQWNAWBWMWQWRUEUFUGUHUKPWKWPWGMWLWKWMWDWOWFWJWMWDMAVRWM
      CAJZVTWDACANADCOZUITZWKWNWEAWJAUJWKWMWDWBXBQULRUHUMSUNVSWAIZLZWCWBWGXDWLL
      ADJZWBXEKZAHZKZWGXCWLXHVSXCWLLZXEBDJZXGWBXEXJMXCWCABDNZUOXIXJXJAHZXGXCWCX
      JXLKZWBWCXCXMBDAUPUQURXJXFAWBXEXJXKUEUFUGUKUSVSXHWGMXCWLVSXEWDXGWFVRXEWDM
      AACDNTZXFWEACAVSXEWDWBXNQUTRVBUMSVSIZWALZWCWBWGXPWLLWTWBWTKZAHZKZWGXOWLXS
      WAXOWLLZWTCBJZXRWBWTYAMXOWCABCOZUOXTYAYAAHZXRXOWCYAYCKZWBXOWCYDCBAUPVAURY
      AXQAWBWTYAYBUEUFUGUKVCWAXSWGMXOWLWAWTWDXRWFVTWTWDMAXATZXQWEADAWAWTWDWBYEQ
      UTRVDUMSXOXCLZWHWCYFWGWBYFFDGZFVEWGFDVFYFYGWGFYFECGZEVEYGWGKZECVFYFYHYIEY
      FYHYGWGYFYHYGLZLZEFJZWBYLKZAHZKWGYLYMAYLWBVGVHYKYLWDYNWFYJYLWDMZYFYHYLCFJ
      YGWDECFNFDCOUIZPYKYJAHZYNWFMYKYHAHZYGAHZLZYQYFYJYTXOYHYRXCYGYSACEVIADFVIV
      JVAYHYGAUAVKYQYMWEAYJAUJYQYLWDWBYJYOAYPTQULVLRVMSVNVOVNVOVPVPVQ $.
      $( [22-Jan-2007] $)
  $}

  ${
    ax11f.1 $e |- ( ph -> A. x ph ) $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  We can start with any formula ` ph ` in which ` x ` is
       not free. $)
    ax11f $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wi ax-1 alrimi a1ii ) BCEZBFGLALAHZBFHAMBDALIJK $.
      $( [21-Jan-2007] $)
  $}

  ${
    ax11indn.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Negation case. $)
    ax11indn $p |- ( -. A. x x = y ->
               ( x = y -> ( -. ph -> A. x ( x = y -> -. ph ) ) ) ) $=
      ( weq wal wn wi wex 19.8a exanali hbn1 con3 syl6 com23 alrimd syl5bi syl5
      wa exp3a ) BCEZBFGZUAAGZUAUCHZBFZUAUCSZUFBIZUBUEUFBJUGUAAHZBFZGZUBUEUAABK
      UBUJUDBUABLUHBLUBUAUJUCUBUAAUIHUJUCHDAUIMNOPQRT $.
      $( [21-Jan-2007] $)

    ${
      ax11indi.2 $e |- ( -. A. x x = y ->
                 ( x = y -> ( ps -> A. x ( x = y -> ps ) ) ) ) $.
      $( Induction step for constructing a substitution instance of ~ ax-11o
         without using ~ ax-11o .  Implication case. $)
      ax11indi $p |- ( -. A. x x = y ->
           ( x = y -> ( ( ph -> ps ) -> A. x ( x = y -> ( ph -> ps ) ) ) ) ) $=
        ( weq wal wn wi wa ax11indn imp pm2.21 imim2i alimi syl6 ax-1 jad ex )
        CDGZCHIZUAABJZUAUCJZCHZJUBUAKZABUEUFAIZUAUGJZCHZUEUBUAUGUIJACDELMUHUDCU
        GUCUAABNOPQUFBUABJZCHZUEUBUABUKJFMUJUDCBUCUABAROPQST $.
        $( [21-Jan-2007] $)
    $}
  $}

  ${
    ax11indalem.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Lemma for ~ ax11inda2 and ~ ax11inda . $)
    ax11indalem $p |- ( -. A. y y = z -> ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) ) $=
      ( weq wal wn wi ax-1 a5i a1i biidd a1d wa alequcom con3i imp hbnae hban
      dral1 imbi2d dral2 3imtr4d alequcoms adantr simplr ax-12 syl2an hba1 ax-4
      adantlr sylan2 alimd syl2anc ax-7 alrimi 19.21t syl albid syl5ib ad2antrr
      wb syld exp31 pm2.61ian ) BDFBGZCDFCGZHZBCFZBGHZVJADGZVJVLIZBGZIZIZIZVGVQ
      VIVGVPVKVGVOVJVODBDBFDGZABGZVJVSIZBGZVLVNVSWAIVRAVTBVSVJJKLAADBVRAMUAZVMV
      TDBBVRVLVSVJWBUBUCUDUENNUFVGHZVIOZVKVJVOWDVKOVJOZVLVJAIZBGZDGZVNWEVKVJDGZ
      VLWHIWDVKVJUGWDVJWIVKWDVJWIWCVRHZDCFDGZHZVJWIIZVIVRVGDBPQWKVHDCPQWJWLWMBC
      DUHRUIZRULVKWIOAWGDVKWIDBCDSVJDUJTWIVKVJAWGIZVJDUKVKVJWOERUMUNUOWDWHVNIVK
      VJWHWFDGZBGWDVNWFDBUPWDWPVMBWCVIBBDBSCDBSTWDWMDGWPVMVCWDWMDWCVIDBDDSCDDST
      WNUQVJADURUSUTVAVBVDVEVF $.
      $( [24-Jan-2007] $)
  $}

  ${
    $d z y $.
    ax11inda2.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( A proof of ~ ax11inda2 that is slightly more direct. $)
    ax11inda2ALT $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi ax-1 a5i a1i biidd dral1 imbi2d dral2 a1d wa imp hbnae wb
      3imtr4d alequcoms simplr dveeq1 nalequcoms adantlr hba1 hban sylan2 alimd
      ax-4 syl2anc ax-7 alrimi 19.21t albid syl5ib ad2antrr syld exp31 pm2.61i
      syl ) BDFBGZBCFZBGHZVEADGZVEVGIZBGZIZIZIVDVKVFVDVJVEVJDBDBFDGZABGZVEVMIZB
      GZVGVIVMVOIVLAVNBVMVEJKLAADBVLAMNZVHVNDBBVLVGVMVEVPOPUBUCQQVDHZVFVEVJVQVF
      RVERZVGVEAIZBGZDGZVIVRVFVEDGZVGWAIVQVFVEUDVQVEWBVFVQVEWBVEWBIZDBDBCUEUFZS
      UGVFWBRAVTDVFWBDBCDTVEDUHUIWBVFVEAVTIZVEDULVFVEWEESUJUKUMVQWAVIIVFVEWAVSD
      GZBGVQVIVSDBUNVQWFVHBBDBTVQWCDGWFVHUAVQWCDBDDTWDUOVEADUPVCUQURUSUTVAVB $.
      $( [4-May-2007] $)

    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  When ` z ` and ` y ` are
       distinct, this theorem avoids the dummy variables needed by the more
       general ~ ax11inda . $)
    ax11inda2 $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi ax-1 a16g syl5 a1d ax11indalem pm2.61i ) CDFCGZBCFZBGHZQA
      DGZQSIZBGZIZIZIPUCRPUBQSTPUASQJTCDBKLMMABCDENO $.
      $( [24-Jan-2007] $)
  $}

  ${
    $d w ph $.  $d w x $.  $d w y $.  $d w z $.
    ax11inda.1 $e |- ( -. A. x x = w ->
               ( x = w -> ( ph -> A. x ( x = w -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  (When ` z ` and ` y `
       are distinct, ~ ax11inda2 may be used instead to avoid the dummy
       variable ` w ` in the proof.) $)
    ax11inda $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi wex a9e wa ax11inda2 wb dveeq2 imp albid syl imbi12d hba1
      equequ2 a4s notbid adantl imbi1d imbi2d mpbii ex exlimdv mpi pm2.43i ) BC
      GZBHZIZUMADHZUMUPJZBHZJZJZUOECGZEKUOUTJZECLUOVAVBEUOVAVBUOVAMZBEGZBHZIZVD
      UPVDUPJZBHZJZJZJVBABEDFNVCVFUOVJUTVCVABHZVFUOOUOVAVKBCEPQZVKVEUNVKVDUMBVA
      BUAZVAVDUMOZBECBUBZUCZRUDSVCVDUMVIUSVAVNUOVOUEVCVHURUPVCVKVHUROVLVKVGUQBV
      MVKVDUMUPVPUFRSUGTTUHUIUJUKUL $.
      $( [24-Jan-2007] $)
  $}

  $( Part of a study related to ~ ax-12 .  The consequent introduces a new
     variable ` z ` .  There are no distinct variable restrictions. $)
  a12stdy1 $p |- ( A. x x = y -> E. x y = z ) $=
    ( weq wal wex a9e wn ax-10o con3d df-ex 3imtr4g mpi ) ABDAEZBCDZBFZOAFZBCGN
    OHZBEZHRAEZHPQNTSRABIJOBKOAKLM $.
    $( [14-Jan-2008] $)

  $( Part of a study related to ~ ax-12 .  The consequent is quantified with a
     different variable.  There are no distinct variable restrictions. $)
  a12stdy2 $p |- ( A. z ( z = x /\ x = y ) -> A. y y = x ) $=
    ( weq wa wal 19.26 ax-10o alequcom syl6 imp sylbi ) CADZABDZECFMCFZNCFZEBAD
    BFZMNCGOPQOPNAFQNCAHABIJKL $.
    $( [14-Jan-2008] $)

  $( Part of a study related to ~ ax-12 .  The consequent introduces two new
     variables.  There are no distinct variable restrictions. $)
  a12stdy3 $p |- ( A. z ( z = x /\ x = y ) -> A. v E. y x = w ) $=
    ( weq wa wal wex a12stdy2 hbae a12stdy1 alimi 3syl ) CAFABFGCHBAFBHZOEHADFB
    IZEHABCJBAEKOPEBADLMN $.
    $( [14-Jan-2008] $)

  $( Part of a study related to ~ ax-12 .  The second antecedent of ~ ax-12 is
     replaced.  There are no distinct variable restrictions. $)
  a12stdy4 $p |- ( -. A. z z = x -> ( A. y z = x ->
           ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wn wi wa ax-10o alequcoms con3d impcom pm2.21d ax-12 a1dd pm2.61d
    ex ) CADZCEZFZCBDCEZRBEZABDZUCCEGZGZTUAUETUAHUBUDUATUBFUAUBSUBSGBCRBCIJKLMQ
    TUAFUDUBABCNOP $.
    $( [14-Jan-2008] $)

  $( Proof of first hypothesis of ~ a12study . $)
  a12lem1 $p |- ( -. A. z z = y ->
                  ( A. z ( z = x -> z = y ) -> x = y ) ) $=
    ( weq wal wn wi wb equequ1 imbi12d a4s dral2 equid a1bi biimpri syl6bi hbn1
    a1d wa hban hbth a1i ax-12 imp hbimd alrimi equtr ax-8 imim12d ax-gen 19.26
    a4imt sylbir sylancl mpii ex pm2.61i ) CADZCEZCBDZCEFZURUTGZCEZABDZGZGUSVEV
    AUSVCAADZVDGZCEZVDVBVGCACURVBVGHCURURVFUTVDCAAICABIJKLVGVDCVDVGVFVDAMZNOKPR
    USFZVAVEVJVASZVCVFVDVIVKVGVHGZCEZURVBVGGGZCEZVCVGGZVKVLCVJVACURCQUTCQTZVKVF
    VDCVQVFVFCEGVKVFCVIUAUBVJVAVDVDCEGABCUCUDUEUFVNCURVFURUTVDCAAUGCABUHUIUJVMV
    OSVLVNSCEVPVLVNCUKVBVGCAULUMUNUOUPUQ $.
    $( [15-Jan-2008] $)

  $( Proof of second hypothesis of ~ a12study . $)
  a12lem2 $p |- ( A. z ( z = x -> -. z = y ) -> -. x = y ) $=
    ( weq wn wi wal wa wex equcom imbi1i imnan bitri albii alnex equvini con3i
    sylbi ) CADZCBDZEZFZCGZACDZTHZCIZEZABDZEUCUEEZCGUGUBUICUBUDUAFUISUDUACAJKUD
    TLMNUECOMUHUFABCPQR $.
    $( [15-Jan-2008] $)

  ${
    a12study.1 $e |- ( -. A. z z = y
         -> ( A. z ( z = x -> z = y ) -> x = y ) ) $.
    a12study.2 $e |- ( A. z ( z = x -> -. z = y ) -> -. x = y ) $.
    $( Rederivation of axiom ~ ax-12 from two shorter formulas, without using
       ~ ax-12 .  See ~ a12lem1 and ~ a12lem2 for the proofs of the hypotheses
       (using ~ ax-12 ).  This is the only known breakdown of ~ ax-12 into
       shorter formulas.  See ~ a12studyALT for an alternate proof.  Note that
       the proof depends on ~ ax-11o , whose proof ~ ax11o depends on ~ ax-12 ,
       meaning that we would have to replace ~ ax-11 with ~ ax-11o in an
       axiomatization that uses the hypotheses in place of ~ ax-12 .  Whether
       this can be avoided is an open problem. $)
    a12study $p |- ( -. A. z z = x -> ( -. A. z z = y
                     -> ( x = y -> A. z x = y ) ) ) $=
      ( weq wa wex wal wn imnan equid1 ax-8 mpi imim1i sylbir alimi hbn1 hba1
      wi con2i df-ex sylibr hban ax-11o syl5 imp3a alrimd sylan9 exlimd ex syl7
      syl ) ABFZACFZCBFZGZCHZCAFZCIJZUPCIJZUNCIZUNUQJZCIZJURVDUNVDUSUPJZTZCIUNJ
      VCVFCVCUOVETVFUOUPKUSUOVEUSCCFUOCLCACMNOPQEUMUAUQCUBUCUTVAURVBTUTVAGUQVBC
      UTVACUSCRUPCRZUDUNCSUTUQUSUPTZCIZVAVBUTUOUPVIUOUSUTUPVITUOAAFUSALACAMNUPC
      AUEUFUGVAVIUNCVGVHCSDUHUIUJUKUL $.
      $( [15-Jan-2008] $)

    $( Alternate proof of ~ a12study , also without using ~ ax-12 . $)
    a12studyALT $p |- ( -. A. z z = x -> ( -. A. z z = y
             -> ( x = y -> A. z x = y ) ) ) $=
      ( weq wal wn wi wa hbn1 hban con3d wex exnal hba1 ax-11o ax11indn syl5bir
      annim a5i syl8 imp3a exlimd sylan9r hbnd notnot albii 3imtr4g ex ) CAFZCG
      HZCBFZCGHZABFZUOCGZIULUNJZUOHZHZUSCGUOUPUQURCULUNCUKCKZUMCKLUNURUKUMIZCGZ
      HZULURCGZUNVBUODMVCVAHZCNULVDVACOULVEVDCUTURCPVEUKUMHZJULVDUKUMTULUKVFVDU
      LUKVFUKVFIZCGVDUMCAUMCAQRVGURCEUAUBUCSUDSUEUFUOUGZUOUSCVHUHUIUJ $.
      $( [17-Jan-2008] $)
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.
    a12study2.1 $e |- ( -. A. x x = z -> ( w = z -> A. x w = z ) ) $.
    a12study2.2 $e |- ( -. A. x x = y -> ( w = y -> A. x w = y ) ) $.
    $( Reprove ~ ax-12 using ~ dvelimfALT2 , showing that ~ ax-12 can be
       replaced by ~ dveeq2 (whose needed instances are the hypotheses here) if
       we allow distinct variables in axioms other than ~ ax-17 .  (Contributed
       by Andrew Salmon, 21-Jul-2011.) $)
    a12study2 $p |- ( -. A. x x = y
      -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $=
      ( cv wceq wal wn hbn1 hbim1 ax-17 equequ1 imbi2d dvelimfALT2 19.21 syl6ib
      wi pm2.86d ) AGZBGZHAIJZUACGZHZAIJZUBUDHZUGAIZUCUFUGSZUIAIUFUHSUFDGZUDHZS
      UIABDUFUKAUEAKZELUIDMUJUBHUKUGUFDBCNOFPUFUGAULQRT $.
      $( [21-Jul-2011] $)
  $}

  ${
    a12study3.1 $e |- ( x = y -> E. z ( x = z /\ z = y ) ) $.
    a12study3.2 $e |- ( A. z ( z = x <-> z = y ) -> x = y ) $.
    $( Rederivation of axiom ~ ax-12 from two other formulas, without using
       ~ ax-12 .  See ~ equvini and ~ equveli for the proofs of the hypotheses
       (using ~ ax-12 ).  Although the second hypothesis (when expanded to
       primitives) is longer than ~ ax-12 , an open problem is whether it can
       be derived without ~ ax-12 or from a simpler axiom.

       Note also that the proof depends on ~ ax-11o , whose proof ~ ax11o
       depends on ~ ax-12 , meaning that we would have to replace ~ ax-11 with
       ~ ax-11o in an axiomatization that uses the hypotheses in place of
       ~ ax-12 .  Whether this can be avoided is an open problem. $)
    a12study3 $p |- ( -. A. z z = x -> ( -. A. z z = y
       -> ( x = y -> A. z x = y ) ) ) $=
      ( weq wal wn wi wa wb wex hbn1 hba1 equid1 ax-8 ax-11o syl5 imp3a exlimd
      mpi syl7 ancomsd anim12ii albiim syl6ibr a5i syl6 ex ) CAFZCGHZCBFZCGHZAB
      FZUNCGZIUKUMJZUNUJULKZCGZUOUPUNUJULIZCGZULUJIZCGZJZURUNACFZULJZCLZUPVCDUK
      VFUTUMVBUKVEUTCUJCMUSCNUKVDULUTVDUJUKULUTIVDAAFUJAOACAPUAZULCAQRSTUMVEVBC
      ULCMVACNUMULVDVBUMULVDVBVDUJUMULVBVGUJCBQUBSUCTUDRUJULCUEUFUQUNCEUGUHUI
      $.
      $( [1-Mar-2013] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Existential uniqueness
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new symbols needed for uniqueness notation. $)
  $c E! $.  $( Backwards E exclamation point. $)
  $c E* $.  $( Backwards E superscript *. $)

  $( Extend wff definition to include existential uniqueness ("there exists a
     unique ` x ` such that ` ph ` "). $)
  weu $a wff E! x ph $.

  $( Extend wff definition to include uniqueness ("there exists at most one
     ` x ` such that ` ph ` "). $)
  wmo $a wff E* x ph $.

  ${
    $d w x y $.  $d x z $.  $d y ph $.  $d w z ph $.
    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  See
       ~ eujustALT for a proof that provides an example of how it can be
       achieved through the use of ~ dvelim .  (The proof was shortened by
       Andrew Salmon, 9-Jul-2011.) $)
    eujust $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw cv wceq wb wal wex equequ2 bibi2d albidv cbvexv bitri ) ABFZCFZGZHZB
      IZCJAPEFZGZHZBIZEJAPDFZGZHZBIZDJTUDCEQUAGZSUCBUIRUBACEBKLMNUDUHEDUAUEGZUC
      UGBUJUBUFAEDBKLMNO $.
      $( [9-Jul-2011] $) $( [11-Mar-2010] $)

    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  While this
       isn't strictly necessary for soundness, the proof provides an example of
       how it can be achieved through the use of ~ dvelim . $)
    eujustALT $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wal wb wex equequ2 bibi2d albidv wn hbnae wi ax-17 notbid dvelim
      a4s df-ex drex1 alrimi nalequcoms a1i cbv2 syl 3bitr4g pm2.61i ) CDFZCGZA
      BCFZHZBGZCIZABDFZHZBGZDIZHUMUQCDUIUMUQHCUIULUPBUIUKUOACDBJKLZSUAUJMZUMMZC
      GZMUQMZDGZMUNURUTVBVDUTUTDGZCGVBVDHUTVECCDCNCDDNUBUTVAVCCDVAVADGODCABEFZH
      ZBGZMZVADCEVIDPECFZVHUMVJVGULBVJVFUKAECBJKLQRUCVIVCCDEVICPEDFZVHUQVKVGUPB
      VKVFUOAEDBJKLQRUIVAVCHOUTUIUMUQUSQUDUEUFQUMCTUQDTUGUH $.
      $( [11-Mar-2010] $)
  $}

  ${
    $d x y $.  $d y ph $.
    $( Define existential uniqueness, i.e.  "there exists exactly one ` x `
       such that ` ph ` ."  Definition 10.1 of [BellMachover] p. 97; also
       Definition *14.02 of [WhiteheadRussell] p. 175.  Other possible
       definitions are given by ~ eu1 , ~ eu2 , ~ eu3 , and ~ eu5 (which in
       some cases we show with a hypothesis ` ph -> A. y ph ` in place of a
       distinct variable condition on ` y ` and ` ph ` ).  Double uniqueness is
       tricky: ` E! x E! y ph ` does not mean "exactly one ` x ` and one
       ` y ` " (see ~ 2eu4 ). $)
    df-eu $a |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $.
  $}

  $( Define "there exists at most one ` x ` such that ` ph ` ."  Here we define
     it in terms of existential uniqueness.  Notation of [BellMachover] p. 460,
     whose definition we show as ~ mo3 .  For other possible definitions see
     ~ mo2 and ~ mo4 . $)
  df-mo $a |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $.

  ${
    $d x y z $.  $d ph z $.
    euf.1 $e |- ( ph -> A. y ph ) $.
    $( A version of the existential uniqueness definition with a hypothesis
       instead of a distinct variable condition. $)
    euf $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      ( vz weu weq wb wal wex df-eu ax-17 hbbi hbal equequ2 bibi2d albidv cbvex
      bitri ) ABFABEGZHZBIZEJABCGZHZBIZCJABEKUBUEECUACBATCDTCLMNUEELECGZUAUDBUF
      TUCAECBOPQRS $.
      $( [12-Aug-1993] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.  $d y ch $.
    eubid.1 $e |- ( ph -> A. x ph ) $.
    eubid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule). $)
    eubid $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( vy weq wb wal wex weu bibi1d albid exbidv df-eu 3bitr4g ) ABDGHZIZDJZGK
      CRIZDJZGKBDLCDLATUBGASUADEABCRFMNOBDGPCDGPQ $.
      $( [9-Jul-1994] $)
  $}

  ${
    $d x ph $.
    eubidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule). $)
    eubidv $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( ax-17 eubid ) ABCDADFEG $.
      $( [9-Jul-1994] $)
  $}

  ${
    eubii.1 $e |- ( ph <-> ps ) $.
    $( Introduce uniqueness quantifier to both sides of an equivalence. $)
    eubii $p |- ( E! x ph <-> E! x ps ) $=
      ( weq weu wb equid hbequid a1i eubid ax-mp ) CCEZACFBCFGCHMABCCCIABGMDJKL
      $.
      $( [9-Jul-1994] $)
  $}

  ${
    $d x y $.  $d y ph $.
    $( Bound-variable hypothesis builder for uniqueness. $)
    hbeu1 $p |- ( E! x ph -> A. x E! x ph ) $=
      ( vy weu weq wb wal wex df-eu hba1 hbex hbxfrbi ) ABDABCEFZBGZCHBABCINBCM
      BJKL $.
      $( [9-Jul-1994] $)
  $}

  ${
    $d y z $.  $d x z $.  $d z ph $.
    hbeu.1 $e |- ( ph -> A. x ph ) $.
    $( Bound-variable hypothesis builder for "at most one."  Note that ` x `
       and ` y ` needn't be distinct (this makes the proof more difficult). $)
    hbeu $p |- ( E! y ph -> A. x E! y ph ) $=
      ( vz weu weq wb wal wex df-eu wi hba1 ax10o alequcoms wn hbnae a1i dveeq1
      syl5 hbbid hbald pm2.61i hbex hbxfrbi ) ACFACEGZHZCIZEJBACEKUHBEBCGBIZUHU
      HBIZLUHUHCIZUIUJUGCMUKUJLCBUHCBNOTUIPZUGBCBCCQULAUFBBCBQAABILULDRBCESUAUB
      UCUDUE $.
      $( [8-Mar-1995] $)
  $}

  ${
    $d y z $.  $d x z $.  $d z ph $.  $d z ps $.
    hbeud.1 $e |- ( ph -> A. x ph ) $.
    hbeud.2 $e |- ( ph -> A. y ph ) $.
    hbeud.3 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction version of ~ hbeu . $)
    hbeud $p |- ( ph -> ( E! y ps -> A. x E! y ps ) ) $=
      ( vz cv wceq wb wal wex weu ax-17 wi wn wa hbnae hban adantr dveeq1 hbbid
      adantl hbald hba1 ax10o alequcoms syl5 pm2.61d2 hbexd df-eu albii 3imtr4g
      ex ) ABDIZHIJZKZDLZHMZUTCLBDNZVACLAUSCHAHOACIUPJCLZUSUSCLZPZAVBQZVDAVERZU
      RCDAVEDFCDDSTVFBUQCAVECECDCSTABBCLPVEGUAVEUQUQCLPACDHUBUDUCUEUOUSUSDLZVBV
      CURDUFVGVCPDCUSDCUGUHUIUJUKBDHULZVAUTCVHUMUN $.
      $( [15-Feb-2013] $)
  $}

  ${
    $d w y z $.  $d ph z w $.  $d w x z $.
    sb8eu.1 $e |- ( ph -> A. y ph ) $.
    $( Variable substitution in uniqueness quantifier.  (Unnecessary distinct
       variable restrictions were removed by Andrew Salmon, 9-Jul-2011.) $)
    sb8eu $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vz vw cv wceq wal wex wsbc weu ax-17 sb8 sbbi hbsb equsb3 hbxfrbi df-eu
      wb hbbi sbequ cbval sblbis albii 3bitri exbii 3bitr4i ) ABGEGZHZTZBIZEJAB
      CGZKZUMUIHZTZCIZEJABLUNCLULUQEULUKBFGZKZFIUKBUMKZCIUQUKBFUKFMNUSUTFCUSABU
      RKZUJBURKZTCAUJBFOVAVBCABFCDPVBURUIHZCFBEQVCCMRUARUTFMUKFCBUBUCUTUPCUJUOA
      BCCBEQUDUEUFUGABESUNCESUH $.
      $( [9-Jul-2011] $) $( [7-Aug-1994] $)
  $}

  ${
    cbveu.1 $e |- ( ph -> A. y ph ) $.
    cbveu.2 $e |- ( ps -> A. x ps ) $.
    cbveu.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.
       (Unnecessary distinct variable restrictions were removed by Andrew
       Salmon, 8-Jun-2011.) $)
    cbveu $p |- ( E! x ph <-> E! y ps ) $=
      ( weu wsb sb8eu sbie eubii bitri ) ACHACDIZDHBDHACDEJNBDABCDFGKLM $.
      $( [9-Jul-2011] $) $( [25-Nov-1994] $)
  $}

  ${
    $d x y $.
    eu1.1 $e |- ( ph -> A. y ph ) $.
    $( An alternate way to express uniqueness used by some authors.  Exercise
       2(b) of [Margaris] p. 110. $)
    eu1 $p |- ( E! x ph <->
                E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) ) $=
      ( wsb weu weq wb wal wex wi wa hbs1 euf sb8eu equcom imbi2i albii 3bitr4i
      sb6rf anbi12i ancom albiim exbii ) ABCEZCFUECBGZHCIZBJABFAUEBCGZKZCIZLZBJ
      UECBABCMNABCDOUKUGBUJALUEUFKZCIZUFUEKCIZLUKUGUJUMAUNUIULCUHUFUEBCPQRABCDT
      UAAUJUBUEUFCUCSUDS $.
      $( [20-Aug-1993] $)
  $}

  ${
    $d x y z $.  $d ph z $.
    mo.1 $e |- ( ph -> A. y ph ) $.
    $( Equivalent definitions of "there exists at most one." $)
    mo $p |- ( E. y A. x ( ph -> x = y ) <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( vz weq wi wal wex wsb wa ax-17 hbim hbal cbv3 syl sylbir alimi wn hbn
      equequ2 imbi2d albidv cbvex hbs1 sbequ2 ax-8 imim12d ancli aaan prth syl6
      sylibr equtr2 2alimi exlimiv impexp bi2.04 bitri 2albii eximi a7s syl5com
      alim exim syl5bi alnex sbequ1 equcoms con3d pm2.21 19.8a 3syl a1d pm2.61i
      impbii ) ABCFZGZBHZCIZAABCJZKZVQGZCHBHZVTABEFZGZBHZEIWDWGVSECWFCBAWECDWEC
      LMZNVSELECFZWFVRBWIWEVQAECBUAUBUCUDWGWDEWGWFWACEFZGZKZCHBHZWDWGWGWKCHZKWM
      WGWNWFWKBCWHWAWJBABCUEZWJBLMZVQWAAWEWJABCUFBCEUGUHOUIWFWKBCWHWPUJUMWLWCBC
      WLWBWEWJKVQAWEWAWJUKBCEUNULUOPUPQWACIZWDVTGWDWAVRGZCHBHZWQVTWCWRBCWCAWAVQ
      GGWRAWAVQUQAWAVQURUSUTWQWABHZCIZWSVTWAWTCWOVAWSWTVSGZCHZXAVTGWRXCCBWRBHXB
      CWAVRBVDRVBWTVSCVEPVCVFWQSZVTWDXDWASZCHZVTWACVGXFASZBHVSVTXEXGCBWABWOTACD
      TCBFAWAAWAGBCABCVHVIVJOXGVRBAVQVKRVSCVLVMQVNVOVP $.
      $( [7-Aug-1994] $)
  $}

  ${
    $d x y $.  $d ph y $.
    $( Existential uniqueness implies existence.  (The proof was shortened by
       Andrew Salmon, 9-Jul-2011.) $)
    euex $p |- ( E! x ph -> E. x ph ) $=
      ( vy weu wsb weq wi wal wa wex ax-17 eu1 exsimpl sylbi ) ABDAABCEBCFGCHZI
      BJABJABCACKLAOBMN $.
      $( [9-Jul-2011] $) $( [15-Sep-1993] $)
  $}

  ${
    $d x y $.
    eumo0.1 $e |- ( ph -> A. y ph ) $.
    $( Existential uniqueness implies "at most one." $)
    eumo0 $p |- ( E! x ph -> E. y A. x ( ph -> x = y ) ) $=
      ( weu weq wb wal wex wi euf bi1 alimi eximi sylbi ) ABEABCFZGZBHZCIAPJZBH
      ZCIABCDKRTCQSBAPLMNO $.
      $( [8-Jul-1994] $)
  $}

  ${
    $d x y $.
    eu2.1 $e |- ( ph -> A. y ph ) $.
    $( An alternate way of defining existential uniqueness.  Definition 6.10 of
       [TakeutiZaring] p. 26. $)
    eu2 $p |- ( E! x ph <->
    ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      ( weu wex wsb wa weq wi wal euex eumo0 mo sylib 19.29r impexp albii 19.21
      jca bitri anbi2i abai bitr4i exbii eu1 sylibr impbii ) ABEZABFZAABCGZHBCI
      ZJZCKZBKZHZUIUJUOABLUIAULJBKCFUOABCDMABCDNOTUPAUKULJZCKZHZBFZUIUPAUNHZBFU
      TAUNBPVAUSBVAAAURJZHUSUNVBAUNAUQJZCKVBUMVCCAUKULQRAUQCDSUAUBAURUCUDUEOABC
      DUFUGUH $.
      $( [8-Jul-1994] $)
  $}

  ${
    $d x y $.
    eu3.1 $e |- ( ph -> A. y ph ) $.
    $( An alternate way to express existential uniqueness. $)
    eu3 $p |- ( E! x ph <->
                ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      ( weu wex wsb wa weq wi wal eu2 mo anbi2i bitr4i ) ABEABFZAABCGHBCIZJCKBK
      ZHPAQJBKCFZHABCDLSRPABCDMNO $.
      $( [8-Jul-1994] $)
  $}

  ${
    euor.1 $e |- ( ph -> A. x ph ) $.
    $( Introduce a disjunct into a uniqueness quantifier. $)
    euor $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( wn weu wo hbn biorf eubid biimpa ) AEZBCFABGZCFLBMCACDHABIJK $.
      $( [21-Oct-2005] $)
  $}

  ${
    $d x ph $.
    $( Introduce a disjunct into a uniqueness quantifier. $)
    euorv $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( ax-17 euor ) ABCACDE $.
      $( [23-Mar-1995] $)
  $}

  ${
    $d x y $.
    mo2.1 $e |- ( ph -> A. y ph ) $.
    $( Alternate definition of "at most one." $)
    mo2 $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( wmo wex weu wi weq wal df-mo alnex pm2.21 alimi 19.8a syl sylbir eumo0
      wn ja eu3 simplbi2com impbii bitri ) ABEABFZABGZHZABCIZHZBJZCFZABKUGUKUEU
      FUKUESASZBJZUKABLUMUJUKULUIBAUHMNUJCOPQABCDRTUFUEUKABCDUAUBUCUD $.
      $( [8-Mar-1995] $)
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    $( Substitution into "at most one".  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    sbmo $p |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph ) $=
      ( vw cv wceq wi wal wex wsbc wmo sbex ax-17 sblim sbalv exbii bitri sbbii
      mo2 3bitr4i ) ADFEFGZHZDIZEJZBCFZKZABUFKZUBHZDIZEJZADLZBUFKUHDLUGUDBUFKZE
      JUKUDEBCMUMUJEUCUIBCDAUBBCUBBNOPQRULUEBCADEAENTSUHDEUHENTUA $.
      $( [2-Sep-2009] $)
  $}

  ${
    $d x y $.
    mo3.1 $e |- ( ph -> A. y ph ) $.
    $( Alternate definition of "at most one."  Definition of [BellMachover]
       p. 460, except that definition has the side condition that ` y ` not
       occur in ` ph ` in place of our hypothesis. $)
    mo3 $p |- ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( wmo weq wi wal wex wsb wa mo2 mo bitri ) ABEABCFZGBHCIAABCJKOGCHBHABCDL
      ABCDMN $.
      $( [8-Mar-1995] $)
  $}

  ${
    $d x y $.  $d y ph $.
    mo4f.1 $e |- ( ps -> A. x ps ) $.
    mo4f.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( "At most one" expressed using implicit substitution. $)
    mo4f $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( wmo wsb wa weq wi wal ax-17 mo3 sbie anbi2i imbi1i 2albii bitri ) ACGAA
      CDHZIZCDJZKZDLCLABIZUBKZDLCLACDADMNUCUECDUAUDUBTBAABCDEFOPQRS $.
      $( [10-Apr-2004] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    mo4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( "At most one" expressed using implicit substitution. $)
    mo4 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( ax-17 mo4f ) ABCDBCFEG $.
      $( [26-Jul-1995] $)
  $}

  ${
    mobid.1 $e |- ( ph -> A. x ph ) $.
    mobid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for "at most one" quantifier (deduction rule). $)
    mobid $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( wex weu wi wmo exbid eubid imbi12d df-mo 3bitr4g ) ABDGZBDHZICDGZCDHZIB
      DJCDJAPRQSABCDEFKABCDEFLMBDNCDNO $.
      $( [8-Mar-1995] $)
  $}

  ${
    mobii.1 $e |- ( ps <-> ch ) $.
    $( Formula-building rule for "at most one" quantifier (inference rule). $)
    mobii $p |- ( E* x ps <-> E* x ch ) $=
      ( weq wmo wb equid hbequid a1i mobid ax-mp ) CCEZACFBCFGCHMABCCCIABGMDJKL
      $.
      $( [9-Mar-1995] $)
  $}

  $( Bound-variable hypothesis builder for "at most one." $)
  hbmo1 $p |- ( E* x ph -> A. x E* x ph ) $=
    ( wmo wex weu wi df-mo hbe1 hbeu1 hbim hbxfrbi ) ABCABDZABEZFBABGLMBABHABIJ
    K $.
    $( [8-Mar-1995] $)

  ${
    hbmo.1 $e |- ( ph -> A. x ph ) $.
    $( Bound-variable hypothesis builder for "at most one." $)
    hbmo $p |- ( E* y ph -> A. x E* y ph ) $=
      ( wmo wex weu wi df-mo hbex hbeu hbim hbxfrbi ) ACEACFZACGZHBACINOBABCDJA
      BCDKLM $.
      $( [9-Mar-1995] $)
  $}

  ${
    cbvmo.1 $e |- ( ph -> A. y ph ) $.
    cbvmo.2 $e |- ( ps -> A. x ps ) $.
    cbvmo.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitition.
       (Unnecessary distinct variable restrictions were removed by Andrew
       Salmon, 8-Jun-2011.) $)
    cbvmo $p |- ( E* x ph <-> E* y ps ) $=
      ( wex weu wi wmo cbvex cbveu imbi12i df-mo 3bitr4i ) ACHZACIZJBDHZBDIZJAC
      KBDKQSRTABCDEFGLABCDEFGMNACOBDOP $.
      $( [9-Jul-2011] $) $( [9-Mar-1995] $)
  $}

  ${
    $d x y $.  $d y ph $.
    $( Uniqueness in terms of "at most one." $)
    eu5 $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $=
      ( vy weu wex weq wi wal wa wmo ax-17 eu3 mo2 anbi2i bitr4i ) ABDABEZABCFG
      BHCEZIPABJZIABCACKZLRQPABCSMNO $.
      $( [23-Mar-1995] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    eu4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Uniqueness using implicit substitution. $)
    eu4 $p |- ( E! x ph <-> ( E. x ph /\
             A. x A. y ( ( ph /\ ps ) -> x = y ) ) ) $=
      ( weu wex wmo wa weq wi wal eu5 mo4 anbi2i bitri ) ACFACGZACHZIQABICDJKDL
      CLZIACMRSQABCDENOP $.
      $( [26-Jul-1995] $)
  $}

  $( Existential uniqueness implies "at most one." $)
  eumo $p |- ( E! x ph -> E* x ph ) $=
    ( weu wex wmo eu5 simprbi ) ABCABDABEABFG $.
    $( [23-Mar-1995] $)

  ${
    eumoi.1 $e |- E! x ph $.
    $( "At most one" inferred from existential uniqueness. $)
    eumoi $p |- E* x ph $=
      ( weu wmo eumo ax-mp ) ABDABECABFG $.
      $( [5-Apr-1995] $)
  $}

  $( Existence in terms of "at most one" and uniqueness. $)
  exmoeu $p |- ( E. x ph <-> ( E* x ph -> E! x ph ) ) $=
    ( wex wmo weu wi df-mo biimpi com12 biimpri euex imim12i peirce syl impbii
    ) ABCZABDZABEZFZQPRQPRFZABGZHISTPFPTQRPQTUAJABKLPRMNO $.
    $( [5-Apr-2004] $)

  $( Existence implies "at most one" is equivalent to uniqueness. $)
  exmoeu2 $p |- ( E. x ph -> ( E* x ph <-> E! x ph ) ) $=
    ( weu wex wmo eu5 baibr ) ABCABDABEABFG $.
    $( [5-Apr-2004] $)

  $( Absorption of existence condition by "at most one." $)
  moabs $p |- ( E* x ph <-> ( E. x ph -> E* x ph ) ) $=
    ( wex weu wi wmo pm5.4 df-mo imbi2i 3bitr4ri ) ABCZKABDZEZEMKABFZENKLGNMKAB
    HZIOJ $.
    $( [4-Nov-2002] $)

  $( Something exists or at most one exists. $)
  exmo $p |- ( E. x ph \/ E* x ph ) $=
    ( wex wmo wn weu wi pm2.21 df-mo sylibr orri ) ABCZABDZLELABFZGMLNHABIJK $.
    $( [8-Mar-1995] $)

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" is preserved through implication (notice wff reversal). $)
    immo $p |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) ) $=
      ( vy wi wal weq wex wmo imim1 al2imi eximdv ax-17 mo2 3imtr4g ) ABEZCFZBC
      DGZEZCFZDHAREZCFZDHBCIACIQTUBDPSUACABRJKLBCDBDMNACDADMNO $.
      $( [22-Apr-1995] $)
  $}

  ${
    immoi.1 $e |- ( ph -> ps ) $.
    $( "At most one" is preserved through implication (notice wff reversal). $)
    immoi $p |- ( E* x ps -> E* x ph ) $=
      ( wi wmo immo mpg ) ABEBCFACFECABCGDH $.
      $( [15-Feb-2006] $)
  $}

  ${
    $d x y $.  $d x y ph $.  $d y ps $.
    $( Move antecedent outside of "at most one." $)
    moimv $p |- ( E* x ( ph -> ps ) -> ( ph -> E* x ps ) ) $=
      ( vy wi wmo weq wal wex ax-1 a1i imim1d alimdv eximdv ax-17 3imtr4g com12
      mo2 ) AABEZCFZBCFZASCDGZEZCHZDIBUBEZCHZDITUAAUDUFDAUCUECABSUBBSEABAJKLMNS
      CDSDORBCDBDORPQ $.
      $( [28-Jul-1995] $)
  $}

  $( Uniqueness implies "at most one" through implication. $)
  euimmo $p |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) ) $=
    ( weu wmo wi wal eumo immo syl5 ) BCDBCEABFCGACEBCHABCIJ $.
    $( [22-Apr-1995] $)

  $( Add existential uniqueness quantifiers to an implication.  Note the
     reversed implication in the antecedent.  (The proof was shortened by
     Andrew Salmon, 14-Jun-2011.) $)
  euim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) ) $=
    ( wex wi wal wa weu wmo ax-1 euimmo anim12ii eu5 syl6ibr ) ACDZABECFZGBCHZO
    ACIZGACHOQOPROQJABCKLACMN $.
    $( [14-Jun-2011] $) $( [19-Oct-2005] $)

  $( "At most one" is still the case when a conjunct is added. $)
  moan $p |- ( E* x ph -> E* x ( ps /\ ph ) ) $=
    ( wa simpr immoi ) BADACBAEF $.
    $( [22-Apr-1995] $)

  ${
    moani.1 $e |- E* x ph $.
    $( "At most one" is still true when a conjunct is added. $)
    moani $p |- E* x ( ps /\ ph ) $=
      ( wmo wa moan ax-mp ) ACEBAFCEDABCGH $.
      $( [9-Mar-1995] $)
  $}

  $( "At most one" is still the case when a disjunct is removed. $)
  moor $p |- ( E* x ( ph \/ ps ) -> E* x ph ) $=
    ( wo orc immoi ) AABDCABEF $.
    $( [5-Apr-2004] $)

  $( "At most one" imports disjunction to conjunction.  (The proof was
     shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran1 $p |- ( ( E* x ph \/ E* x ps ) -> E* x ( ph /\ ps ) ) $=
    ( wmo wa simpl immoi moan jaoi ) ACDABEZCDBCDJACABFGBACHI $.
    $( [9-Jul-2011] $) $( [5-Apr-2004] $)

  $( "At most one" exports disjunction to conjunction.  (The proof was
     shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran2 $p |- ( E* x ( ph \/ ps ) -> ( E* x ph /\ E* x ps ) ) $=
    ( wo wmo moor olc immoi jca ) ABDZCEACEBCEABCFBJCBAGHI $.
    $( [9-Jul-2011] $) $( [5-Apr-2004] $)

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    moanim.1 $e |- ( ph -> A. x ph ) $.
    $( Introduction of a conjunct into "at most one" quantifier. $)
    moanim $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( vy wa weq wi wal wex impexp albii 19.21 bitri exbii ax-17 imbi2i 19.37v
      wmo mo2 bitr4i 3bitr4i ) ABFZCEGZHZCIZEJABUDHZCIZHZEJZUCCSABCSZHZUFUIEUFA
      UGHZCIUIUEUMCABUDKLAUGCDMNOUCCEUCEPTULAUHEJZHUJUKUNABCEBEPTQAUHERUAUB $.
      $( [3-Dec-2001] $)

    $( Introduction of a conjunct into uniqueness quantifier.  (The proof was
       shortened by Andrew Salmon, 9-Jul-2011.) $)
    euan $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( wa weu wex wmo simpl exlimi adantr simpr eximi hbe1 ancrd impbid2 mobid
      a1d biimpa eu5 jca32 anbi2i 3imtr4i ibar eubid impbii ) ABEZCFZABCFZEZUGC
      GZUGCHZEZABCGZBCHZEZEUHUJUMAUNUOUKAULUGACDABIJZKUKUNULUGBCABLZMKUKULUOUKU
      GBCUGCNUKUGBURUKBAUKABUQROPQSUAUGCTUIUPABCTUBUCAUIUHABUGCDABUDUESUF $.
      $( [9-Jul-2011] $) $( [19-Feb-2005] $)
  $}

  ${
    $d x y ph $.  $d y ps $.
    $( Introduction of a conjunct into "at most one" quantifier. $)
    moanimv $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( ax-17 moanim ) ABCACDE $.
      $( [23-Mar-1995] $)
  $}

  $( Nested "at most one" and uniqueness quantifiers. $)
  moaneu $p |- E* x ( ph /\ E! x ph ) $=
    ( weu wa wmo wi eumo hbeu1 moanim mpbir ancom mobii ) AABCZDZBEMADZBEZPMABE
    FABGMABABHIJNOBAMKLJ $.
    $( [25-Jan-2006] $)

  $( Nested "at most one" quantifiers. $)
  moanmo $p |- E* x ( ph /\ E* x ph ) $=
    ( wmo wa wi id hbmo1 moanim mpbir ancom mobii ) AABCZDZBCLADZBCZOLLELFLABAB
    GHIMNBALJKI $.
    $( [25-Jan-2006] $)

  ${
    $d x ph $.
    $( Introduction of a conjunct into uniqueness quantifier. $)
    euanv $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( ax-17 euan ) ABCACDE $.
      $( [23-Mar-1995] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( "At most one" picks a variable value, eliminating an existential
       quantifier. $)
    mopick $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
      ( vy wa wex wmo wi wsb ax-17 hbs1 hban weq sbequ12 anbi12d cbvex wal ax-4
      mo3 sylbi a4s sbequ2 imim2i exp3a com4t imp syl5 exlimiv impcom ) ABEZCFZ
      ACGZABHZUKACDIZBCDIZEZDFULUMHZUJUPCDUJDJUNUOCACDKBCDKLCDMZAUNBUOACDNBCDNO
      PUPUQDULAUNEZURHZUPUMULUTDQZCQUTACDADJSVAUTCUTDRUATUNUOUTUMHUTAUNUOBUTAUN
      UOBHZURVBUSBCDUBUCUDUEUFUGUHTUI $.
      $( [27-Jan-1997] $)
  $}

  $( Existential uniqueness "picks" a variable value for which another wff is
     true.  If there is only one thing ` x ` such that ` ph ` is true, and
     there is also an ` x ` (actually the same one) such that ` ph ` and ` ps `
     are both true, then ` ph ` implies ` ps ` regardless of ` x ` .  This
     theorem can be useful for eliminating existential quantifiers in a
     hypothesis.  Compare Theorem *14.26 in [WhiteheadRussell] p. 192. $)
  eupick $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
    ( weu wmo wa wex wi eumo mopick sylan ) ACDACEABFCGABHACIABCJK $.
    $( [10-Jul-1994] $)

  $( Version of ~ eupick with closed formulas. $)
  eupicka $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> A. x ( ph -> ps ) ) $=
    ( weu wa wex wi hbeu1 hbe1 hban eupick alrimi ) ACDZABEZCFZEABGCMOCACHNCIJA
    BCKL $.
    $( [6-Sep-2008] $)

  $( Existential uniqueness "pick" showing wff equivalence. $)
  eupickb $p |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) ->
               ( ph <-> ps ) ) $=
    ( weu wa wex w3a wi eupick 3adant2 3simpc pm3.22 eximi anim2i 3syl impbid )
    ACDZBCDZABEZCFZGZABQTABHRABCIJUARTERBAEZCFZEBAHQRTKTUCRSUBCABLMNBACIOP $.
    $( [25-Nov-1994] $)

  $( Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 11-Jul-2011.) $)
  eupickbi $p |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) ) $=
    ( weu wa wex wi wal eupicka ex hba1 wb ancl simpl impbid1 eubid euex syl6bi
    a4s com12 impbid ) ACDZABEZCFZABGZCHZUBUDUFABCIJUFUBUDUFUBUCCDUDUFAUCCUECKU
    EAUCLCUEAUCABMABNOSPUCCQRTUA $.
    $( [11-Jul-2011] $)

  $( "At most one" can show the existence of a common value.  In this case we
     can infer existence of conjunction from a conjunction of existence, and it
     is one way to achieve the converse of ~ 19.40 .  (The proof was shortened
     by Andrew Salmon, 9-Jul-2011.) $)
  mopick2 $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) ->
                E. x ( ph /\ ps /\ ch ) ) $=
    ( wmo wa wex w3a hbmo1 hbe1 mopick ancld anim1d df-3an syl6ibr eximd 3impia
    hban ) ADEZABFZDGZACFZDGABCHZDGSUAFZUBUCDSUADADITDJRUDUBTCFUCUDATCUDABABDKL
    MABCNOPQ $.
    $( [9-Jul-2011] $) $( [5-Apr-2004] $)

  $( Introduce or eliminate a disjunct in a uniqueness quantifier.  (The proof
     was shortened by Andrew Salmon, 9-Jul-2011.) $)
  euor2 $p |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) ) $=
    ( wex wn wo hbe1 hbn wb 19.8a con3i orel1 olc impbid1 syl eubid ) ACDZEZABF
    ZBCQCACGHRAEZSBIAQACJKTSBABLBAMNOP $.
    $( [9-Jul-2011] $) $( [21-Oct-2005] $)

  ${
    moexex.1 $e |- ( ph -> A. y ph ) $.
    $( "At most one" double quantification. $)
    moexex $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( wmo wal wa wex wi hbmo1 hba1 hbe1 hbmo hbim mopick ex exlimi wn a1d ori
      com3r alrimd immo a4sd syl6 hbex exsimpl con3i exmo syl pm2.61i imp ) ACF
      ZBDFZCGZABHZCIZDFZACIZUNUPUSJZJZAVBCUNVACACKUPUSCUOCLURCDUQCMNOOAUNURBJZD
      GZVAAUNVCDEADCENUNURABUNURABJABCPQUBUCVDUOUSCURBDUDUEUFRUTSZVAUNVEUSUPVEU
      RDIZSUSVFUTURUTDADCEUGABCUHRUIVFUSURDUJUAUKTTULUM $.
      $( [3-Dec-2001] $)
  $}

  ${
    $d y ph $.
    $( "At most one" double quantification. $)
    moexexv $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( ax-17 moexex ) ABCDADEF $.
      $( [26-Jan-1997] $)
  $}

  $( Double quantification with "at most one." $)
  2moex $p |- ( E* x E. y ph -> A. y E* x ph ) $=
    ( wex wmo hbe1 hbmo 19.8a immoi alrimi ) ACDZBEABECKCBACFGAKBACHIJ $.
    $( [3-Dec-2001] $)

  $( Double quantification with existential uniqueness.  (The proof was
     shortened by Andrew Salmon, 9-Jul-2011.) $)
  2euex $p |- ( E! x E. y ph -> E. y E! x ph ) $=
    ( wex weu wmo wa eu5 excom hbe1 19.8a immoi df-mo sylib eximd syl5bi impcom
    hbmo wi sylbi ) ACDZBEUABDZUABFZGABEZCDZUABHUCUBUEUBABDZCDUCUEABCIUCUFUDCUA
    CBACJRUCABFUFUDSAUABACKLABMNOPQT $.
    $( [9-Jul-2011] $) $( [3-Dec-2001] $)

  $( Double quantification with existential uniqueness and "at most one." $)
  2eumo $p |- ( E! x E* y ph -> E* x E! y ph ) $=
    ( weu wmo wi euimmo eumo mpg ) ACDZACEZFKBDJBEFBJKBGACHI $.
    $( [3-Dec-2001] $)

  $( Double existential uniqueness. $)
  2eu2ex $p |- ( E! x E! y ph -> E. x E. y ph ) $=
    ( weu wex euex eximi syl ) ACDZBDIBEACEZBEIBFIJBACFGH $.
    $( [3-Dec-2001] $)

  $( A condition allowing swap of "at most one" and existential quantifiers. $)
  2moswap $p |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) ) $=
    ( wmo wal wex wa hbe1 moexex expcom 19.8a pm4.71ri exbii mobii syl6ibr ) AC
    DBEZACFZBDZQAGZBFZCDZABFZCDRPUAQABCACHIJUBTCASBAQACKLMNO $.
    $( [10-Apr-2004] $)

  $( A condition allowing swap of uniqueness and existential quantifiers. $)
  2euswap $p |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) ) $=
    ( wmo wal wex wa weu wi excomim a1i 2moswap anim12d eu5 3imtr4g ) ACDBEZACF
    ZBFZQBDZGABFZCFZTCDZGQBHTCHPRUASUBRUAIPABCJKABCLMQBNTCNO $.
    $( [10-Apr-2004] $)

  $( Double existential uniqueness implies double uniqueness quantification. $)
  2exeu $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $=
    ( wex wmo weu excom hbe1 19.41 19.8a immoi anim2i eximi sylbir sylanb simpl
    wa hbmo eu5 anbi12i adantl anim12i ancoms exbii mobii bitri 3imtr4i ) ACDZB
    DZUHBEZQZABDZCDZULCEZQZQUHACEZQZBDZUQBEZQZUHBFZULCFZQACFZBFZUOUKUTUOURUKUSU
    MUIUNURACBGUIUNQUHUNQZBDURUHUNBULBCABHRIVEUQBUNUPUHAULCABJKLMNOUJUSUIUQUHBU
    HUPPKUAUBUCVAUKVBUOUHBSULCSTVDVCBDZVCBEZQUTVCBSVFURVGUSVCUQBACSZUDVCUQBVHUE
    TUFUG $.
    $( [3-Dec-2001] $)

  ${
    $d x y z w v u $.  $d z w v u ph $.
    $( Two equivalent expressions for double "at most one." $)
    2mo $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
              A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) ->
                   ( x = z /\ y = w ) ) ) $=
      ( vv vu weq wa wi wal wex wsb equequ2 bi2anan9 ax-17 albii bitri 2alimi
      wn imbi2d 2albidv cbvex2v hbs1 hbim hbsb sbequ12 sylan9bbr equequ1 cbval2
      imbi12d biimpi ancli alcom aaan hbal sylibr prth equtr2 anim12i an4s syl6
      syl exlimivv sylbir impexp bi2.04 2albii alrimi 2eximi alrot4 alim al2imi
      sylbi exim alimi syl5com syl5bi alnex notbid biimpri pm2.21 19.8a 19.23bi
      3syl hbn a1d pm2.61i impbii ) ABDHZCEHZIZJZCKZBKZELZDLZAACEMZBDMZIZWLJZEK
      DKZCKBKZWQABFHZCGHZIZJZCKZBKZGLFLXCXIWOFGDEFDHZGEHZIZXGWMBCXLXFWLAXJXDWJX
      KXEWKFDBNGECNOUAUBUCXIXCFGXIXGWSDFHZEGHZIZJZIZEKZDKZCKZBKZXCXIXIXPEKZDKZI
      ZYAXIYCXIYCXGXPBCDEXGDPXGEPZWSXOBWRBDUDZXOBPUEZWSXOCWRBDCACEUDUFZXOCPUEZW
      LAWSXFXOWKAWRWJWSACEUGWRBDUGUHZWJXDXMWKXEXNBDFUICEGUIOUKUJULUMYAXHYBIZDKZ
      BKYDXTYLBXTXRCKZDKYLXRCDUNYMYKDXGXPCEYEYIUOQRQXHYBBDXHDPXPBEYGUPUORUQXSXB
      BCXQXADEXQWTXFXOIWLAXFWSXOURXDXMXEXNWLXDXMIWJXEXNIWKBDFUSCEGUSUTVAVBSSVCV
      DVEWSELZDLZXCWQJXCWSWMJZEKDKZCKBKZYOWQXBYQBCXAYPDEXAAWSWLJJYPAWSWLVFAWSWL
      VGRVHVHYOWSCKZBKZELZDLZYRWQWSYTDEWSYSBYFYHVIVJYRYTWOJZEKZDKZUUAWPJZDKUUBW
      QJYRYPCKZBKZEKDKUUEYPBCDEVKUUHUUCDEUUGYSWNBWSWMCVLVMSVNUUDUUFDYTWOEVOVPUU
      AWPDVOWEVQVRYOTZWQXCUUIWSTZEKZDKZWQUULYNTZDKUUIUUKUUMDWSEVSQYNDVSRUULATZC
      KBKZWOWQUUOUULUUNUUJBCDEUUNDPUUNEPWSBYFWFWSCYHWFWLAWSYJVTUJWAUUNWMBCAWLWB
      SWOWQEWPDWCWDWEVEWGWHWI $.
      $( [2-Feb-2005] $)
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x y z w $.
    2mos.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Double "exists at most one", using implicit substitition. $)
    2mos $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
             A. x A. y A. z A. w ( ( ph /\ ps ) -> ( x = z /\ y = w ) ) ) $=
      ( weq wa wi wal wex wsb 2mo ax-17 sbrim wb expcom sbie 2albii pm5.74ri
      pm5.74d bitr3i anbi2i imbi1i bitri ) ACEHZDFHZIZJDKCKFLELAADFMZCEMZIZUIJZ
      FKEKZDKCKABIZUIJZFKEKZDKCKACDEFNUNUQCDUMUPEFULUOUIUKBAUJBCEBCOUGUJBUGUJJU
      GAJZDFMUGBJZUGADFUGDOPURUSDFUSDOUHUGABUGUHABQGRUBSUCUASUDUETTUF $.
      $( [10-Feb-2005] $)
  $}

  $( Double existential uniqueness.  This theorem shows a condition under which
     a "naive" definition matches the correct one. $)
  2eu1 $p |- ( A. x E* y ph ->
        ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wal weu wex wa wi eu5 exbii mobii anbi12i bitri simprbi anim2i ancoms
    ax-4 sylib com12 immoi hba1 moanim ancrd 2moswap imdistani syl 2eu2ex excom
    syl6 jca jctild an4 syl6ibr 2exeu impbid1 ) ACDZBEZACFZBFZACGZBFZABGZCFZHZU
    TURVEUTURVABGZVCCGZHZVABDZVCCDZHZHZVEUTURVKVHUTVAUQHZBDZURVKIUTVMBGZVNUTUSB
    GZUSBDZHVOVNHUSBJVPVOVQVNUSVMBACJZKUSVMBVRLMNOVNURVIURHVKVNURVIVNURVAHZBDUR
    VIIVSVMBVAURVMURUQVAUQBRPQUAURVABUQBUBUCSUDVIURVJURVIVJABCUETUFUJUGUTVFVGAB
    CUHZUTVFVGVTABCUISUKULVEVFVIHZVGVJHZHVLVBWAVDWBVABJVCCJMVFVIVGVJUMNUNTABCUO
    UP $.
    $( [3-Dec-2001] $)

  $( Double existential uniqueness. $)
  2eu2 $p |- ( E! y E. x ph -> ( E! x E! y ph <-> E! x E. y ph ) ) $=
    ( wex weu wmo wal wi eumo 2moex 2eu1 simpl syl6bi 3syl 2exeu expcom impbid
    wa ) ABDZCEZACEBEZACDBEZTSCFACFBGZUAUBHSCIACBJUCUAUBTRUBABCKUBTLMNUBTUAABCO
    PQ $.
    $( [3-Dec-2001] $)


  $( Double existential uniqueness. $)
  2eu3 $p |- ( A. x A. y ( E* x ph \/ E* y ph ) ->
 ( ( E! x E! y ph /\ E! y E! x ph ) <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wo wal weu wa wex wb hbmo1 19.31 albii hbal 19.32 bitri wi 2eu1 2exeu
    biimpd ancom syl6ib adantld adantrd jaoi ancoms jca impbid1 sylbi ) ABDZACD
    ZECFZBFZUJCFZUKBFZEZACGBGZABGCGZHZACIBGZABICGZHZJUMUNUKEZBFUPULVCBUJUKCACKL
    MUNUKBUJBCABKNOPUPUSVBUNUSVBQUOUNURVBUQUNURVAUTHZVBUNURVDACBRTVAUTUAUBUCUOU
    QVBURUOUQVBABCRTUDUEVBUQURABCSVAUTURACBSUFUGUHUI $.
    $( [3-Dec-2001] $)

  ${
    $d x y z w $.  $d z w ph $.
    $( This theorem provides us with a definition of double existential
       uniqueness ("exactly one ` x ` and exactly one ` y ` ").  Naively one
       might think (incorrectly) that it could be defined by
       ` E! x E! y ph ` .  See ~ 2eu1 for a condition under which the naive
       definition holds and ~ 2exeu for a one-way implication.  See ~ 2eu5 and
       ~ 2eu8 for alternate definitions. $)
    2eu4 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( wex weu wa weq wal ax-17 eu3 anbi12i anbi2i bitri hba1 19.3 19.26 albii
      wi an4 excom anidm jcab 3bitr4ri alcom bitr4i 19.23v 2albii 3bitri 2exbii
      hbe1 hbim aaan eeanv bitr2i ) ACFZBGZABFZCGZHUQBFZUQBDIZTZBJZDFZHZUSCFZUS
      CEIZTZCJZEFZHZHVAVGHZVEVKHZHVAAVBVHHTZCJZBJZEFDFZHURVFUTVLUQBDUQDKLUSCEUS
      EKLMVAVEVGVKUAVMVAVNVRVMVAVAHVAVGVAVAACBUBNVAUCOVRVDVJHZEFDFVNVQVSDEVQAVB
      TZCJZAVHTZBJZHZCJZBJZVCVIHZCJBJVSVQWAWBCJZBJZHZBJZWFWABJZWIBJZHWLWIHZWKVQ
      WMWIWLWIBWHBPQNWAWIBRVQWAWHHZBJWNVPWOBVPVTWBHZCJWOVOWPCAVBVHUDSVTWBCROSWA
      WHBROUEWEWJBWEWACJZWCCJZHWJWAWCCRWQWAWRWIWACVTCPQWBCBUFMOSUGWDWGBCWAVCWCV
      IAVBCUHAVHBUHMUIVCVIBCUQVBCACULVBCKUMUSVHBABULVHBKUMUNUJUKVDVJDEUOUPMUJ
      $.
      $( [3-Dec-2001] $)

    $( An alternate definition of double existential uniqueness (see ~ 2eu4 ).
       A mistake sometimes made in the literature is to use ` E! x E! y ` to
       mean "exactly one ` x ` and exactly one ` y ` ."  (For example, see
       Proposition 7.53 of [TakeutiZaring] p. 53.)  It turns out that this is
       actually a weaker assertion, as can be seen by expanding out the formal
       definitions.  This theorem shows that the erroneous definition can be
       repaired by conjoining ` A. x E* y ph ` as an additional condition.  The
       correct definition apparently has never been published.  ( ` E* ` means
       "exists at most one.") $)
    2eu5 $p |- ( ( E! x E! y ph /\ A. x E* y ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( weu wmo wal wa wex weq 2eu1 pm5.32ri eumo adantl 2moex syl pm4.71i 2eu4
      wi 3bitr2i ) ACFBFZACGBHZIACJZBFZABJZCFZIZUCIUHUDBJABDKCEKITCHBHEJDJIUCUB
      UHABCLMUHUCUHUFCGZUCUGUIUEUFCNOACBPQRABCDESUA $.
      $( [26-Oct-2003] $)
  $}

  ${
    $d x y z w v u $.  $d z w v u ph $.
    $( Two equivalent expressions for double existential uniqueness. $)
    2eu6 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
               E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) ) $=
      ( vu vv wex wa weq wi wal ax-17 hbsb sbequ12 equequ2 bi2anan9 hbim 2exbii
      wsb weu 2eu4 19.29r2 hbs1 sylan9bbr cbvex2 imbi2d 2albidv cbvex2v equequ1
      wb imbi12d cbval2 3bitri anbi12i 2albiim ancom bitri equcom imbi2i impexp
      2mo 2albii hban sbco2 sbcom2 sbbii 3bitr3ri syl6bb anbi2d 19.21-2 3bitr3i
      anbi2i abai 2sb6 anbi1i 3bitr2i bitr4i 3imtr4i 2alimi 2eximi 2exsb sylibr
      bi2 bi1 jca impbii ) ACHZBUAABHCUAIWHBHZABDJZCEJZIZKZCLBLZEHDHZIZAWLUKZCL
      BLZEHDHZABCDEUBWPWSACETZBDTZEHDHZXAXAEFTZDGTZIZDGJZEFJZIZKZFLGLZELDLZIXAX
      JIZEHDHZWPWSXAXJDEUCWIXBWOXKAXABCDEADMAEMZWTBDUDZWTBDCACEUDNZWKAWTWJXAACE
      OWTBDOUEZUFWOABGJZCFJZIZKZCLBLZFHGHXAXHKZELDLZFHGHXKWNYBDEGFXHWMYABCXHWLX
      TAXFWJXRXGWKXSDGBPEFCPQUGUHUIYBYDGFYAYCBCDEYADMYAEMXAXHBXOXHBMZRXAXHCXPXH
      CMZRWLAXAXTXHXQWJXRXFWKXSXGBDGUJCEFUJQULUMSXADEGFVBUNUOWSWLAKZCLBLZWNIZEH
      DHXMWRYIDEWRWNYHIYIAWLBCUPWNYHUQURSXLYIDEXLXAXAWNKZIXAWNIYIXJYJXAXAAIZDBJ
      ZECJZIZKZCLBLXAWMKZCLBLXJYJYOYPBCYOYKWLKYPYNWLYKYLWJYMWKDBUSECUSUOUTXAAWL
      VAURVCYOXIBCGFYOGMYOFMXEXHBXAXDBXOXCDGBXAEFBXONNVDYERXEXHCXAXDCXPXCDGCXAE
      FCXPNNVDYFRXTYKXEYNXHXTAXDXAXTAACFTZBGTZXDXSAYQXRYRACFOYQBGOUEWTEFTZBDTZD
      GTYSBGTXDYRYSBGDYSDMVEYTXCDGWTEFBDVFVGYSYQBGACFEXNVEVGVHVIVJXRYLXFXSYMXGB
      GDPCFEPQULUMXAWMBCXOXPVKVLVMXAWNVNXAYHWNABCDEVOVPVQSVRVSWSWIWOWSYHEHDHWIW
      RYHDEWQYGBCAWLWDVTWAABCDEWBWCWRWNDEWQWMBCAWLWEVTWAWFWGUR $.
      $( [2-Feb-2005] $)
  $}

  $( Two equivalent expressions for double existential uniqueness. $)
  2eu7 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
             E! x E! y ( E. x ph /\ E. y ph ) ) $=
    ( wex weu wa hbe1 hbeu euan ancom eubii 3bitri 3bitr4ri ) ABDZCEZACDZFZBEOP
    BEZFNPFZCEZBEROFOPBNBCABGHITQBTPNFZCEPOFQSUACNPJKPNCACGIPOJLKROJM $.
    $( [19-Feb-2005] $)

  $( Two equivalent expressions for double existential uniqueness.  Curiously,
     we can put ` E! ` on either of the internal conjuncts but not both.  We
     can also commute ` E! x E! y ` using ~ 2eu7 . $)
  2eu8 $p |- ( E! x E! y ( E. x ph /\ E. y ph ) <->
                E! x E! y ( E! x ph /\ E. y ph ) ) $=
    ( wex wa 2eu2 pm5.32i hbeu1 hbeu euan ancom eubii hbe1 3bitri 3bitr4ri 2eu7
    weu 3bitr3ri ) ACDZBQZABQZCQZEZTABDZCQZEUASEZCQZBQZUDSECQBQTUBUEACBFGUBSEZB
    QUBTEUHUCUBSBUABCABHIJUGUIBUGSUAEZCQSUBEUIUFUJCUASKLSUACACMJSUBKNLTUBKOABCP
    R $.
    $( [20-Feb-2005] $)

  ${
    $d x y z $.
    $( Equality has existential uniqueness.  (Contributed by Stefan Allan,
       4-Dec-2008.) $)
    euequ1 $p |- E! x x = y $=
      ( vz weq weu wex wa wi wal a9e equtr2 gen2 equequ1 eu4 mpbir2an ) ABDZAEP
      AFPCBDZGACDHZCIAIABJRACACBKLPQACACBMNO $.
      $( [4-Dec-2008] $)
  $}

  ${
    $d x y $.
    $( Two ways to express "only one thing exists."  The left-hand side
       requires only one variable to express this.  Both sides are false in set
       theory. $)
    exists1 $p |- ( E! x x = x <-> A. x x = y ) $=
      ( weq weu wb wal wex df-eu equid tbt bicom bitri albii exbii hbae 3bitr2i
      19.9 ) AACZADRABCZEZAFZBGSAFZBGUBRABHUBUABSTASSRETRSAIJSRKLMNUBBABBOQP $.
      $( [5-Apr-2004] $)

    $( A condition implying that at least two things exist.  (The proof was
       shortened by Andrew Salmon, 9-Jul-2011.) $)
    exists2 $p |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x ) $=
      ( vy wex wn cv wceq weu wal hbeu1 hba1 wi exists1 ax-16 sylbi exlimd alex
      com12 syl6ib con2d imp ) ABDZAEBDZBFZUDGZBHZEUBUFUCUBUFABIZUCEUFUBUGUFAUG
      BUEBJABKUFUDCFGBIAUGLBCMABCNOPRABQSTUA $.
      $( [9-Jul-2011] $) $( [10-Apr-2004] $)
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
       Appendix:  Typesetting definitions for the tokens in this file
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( $t

/* The '$ t' (no space between '$' and 't') token indicates the beginning
    of the typesetting definition section, embedded in a Metamath
    comment.  There may only be one per source file, and the typesetting
    section ends with the end of the Metamath comment.  The typesetting
    section uses C-style comment delimiters.  Todo:  Allow multiple
    typesetting comments */

/* These are the LaTeX and HTML definitions in the order the tokens are
    introduced in $c or $v statements.  See HELP TEX or HELP HTML in the
    Metamath program. */


/******* Web page format settings *******/

/* Page title, home page link */
htmltitle "Intuitionistic Logic Explorer";
htmlhome '<A HREF="mmil.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="_icon-il.gif" BORDER=0 ALT=' +
    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE>' +
    'Home</FONT></A>';
/* Optional file where bibliographic references are kept */
/* If specified, e.g. "mmset.html", Metamath will hyperlink all strings of the
   form "[rrr]" (where "rrr" has no whitespace) to "mmset.html#rrr" */
/* A warning will be given if the file "mmset.html" with the bibliographical
   references is not present.  It is read in order to check correctness of
   the references. */
htmlbibliography "mmil.html";

/* Variable color key at the bottom of each proof table */
htmlvarcolor '<FONT COLOR="#0000FF">wff</FONT> '
    + '<FONT COLOR="#FF0000">set</FONT> '
    + '<FONT COLOR="#CC33CC">class</FONT>';

/* GIF and Unicode HTML directories - these are used for the GIF version to
   crosslink to the Unicode version and vice-versa */
htmldir "../ilegif/";
althtmldir "../ileuni/";


/******* Symbol definitions *******/

htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 TITLE='(' ALIGN=TOP>";
  althtmldef "(" as "(";
  latexdef "(" as "(";
htmldef ")" as "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 TITLE=')' ALIGN=TOP>";
  althtmldef ")" as ")";
  latexdef ")" as ")";
htmldef "->" as
    " <IMG SRC='to.gif' WIDTH=15 HEIGHT=19 TITLE='-&gt;' ALIGN=TOP> ";
  althtmldef "->" as ' &rarr; ';
  latexdef "->" as "\rightarrow";
htmldef "-." as
    "<IMG SRC='lnot.gif' WIDTH=10 HEIGHT=19 TITLE='-.' ALIGN=TOP> ";
  althtmldef "-." as '&not; ';
  latexdef "-." as "\lnot";
htmldef "wff" as
    "<IMG SRC='_wff.gif' WIDTH=24 HEIGHT=19 TITLE='wff' ALIGN=TOP> ";
  althtmldef "wff" as '<FONT COLOR="#808080">wff </FONT>'; /* was #00CC00 */
  latexdef "wff" as "{\rm wff}";
htmldef "|-" as
    "<IMG SRC='_vdash.gif' WIDTH=10 HEIGHT=19 TITLE='|-' ALIGN=TOP> ";
  althtmldef "|-" as
    '<FONT COLOR="#808080" FACE=sans-serif>&#8866; </FONT>'; /* &vdash; */
    /* Without sans-serif, way too big in FF3 */
  latexdef "|-" as "\vdash";
htmldef "ph" as
    "<IMG SRC='_varphi.gif' WIDTH=11 HEIGHT=19 TITLE='ph' ALIGN=TOP>";
  althtmldef "ph" as '<FONT COLOR="#0000FF"><I>&phi;</I></FONT>';
  latexdef "ph" as "\varphi";
htmldef "ps" as "<IMG SRC='_psi.gif' WIDTH=12 HEIGHT=19 TITLE='ps' ALIGN=TOP>";
  althtmldef "ps" as '<FONT COLOR="#0000FF"><I>&psi;</I></FONT>';
  latexdef "ps" as "\psi";
htmldef "ch" as "<IMG SRC='_chi.gif' WIDTH=12 HEIGHT=19 TITLE='ch' ALIGN=TOP>";
  althtmldef "ch" as '<FONT COLOR="#0000FF"><I>&chi;</I></FONT>';
  latexdef "ch" as "\chi";
htmldef "th" as
    "<IMG SRC='_theta.gif' WIDTH=8 HEIGHT=19 TITLE='th' ALIGN=TOP>";
  althtmldef "th" as '<FONT COLOR="#0000FF"><I>&theta;</I></FONT>';
  latexdef "th" as "\theta";
htmldef "ta" as "<IMG SRC='_tau.gif' WIDTH=10 HEIGHT=19 TITLE='ta' ALIGN=TOP>";
  althtmldef "ta" as '<FONT COLOR="#0000FF"><I>&tau;</I></FONT>';
  latexdef "ta" as "\tau";
htmldef "et" as "<IMG SRC='_eta.gif' WIDTH=9 HEIGHT=19 TITLE='et' ALIGN=TOP>";
  althtmldef "et" as '<FONT COLOR="#0000FF"><I>&eta;</I></FONT>';
  latexdef "et" as "\eta";
htmldef "ze" as "<IMG SRC='_zeta.gif' WIDTH=9 HEIGHT=19 TITLE='ze' ALIGN=TOP>";
  althtmldef "ze" as '<FONT COLOR="#0000FF"><I>&zeta;</I></FONT>';
  latexdef "ze" as "\zeta";
htmldef "si" as
    "<IMG SRC='_sigma.gif' WIDTH=10 HEIGHT=19 TITLE='si' ALIGN=TOP>";
  althtmldef "si" as '<FONT COLOR="#0000FF"><I>&sigma;</I></FONT>';
  latexdef "si" as "\sigma";
htmldef "rh" as "<IMG SRC='_rho.gif' WIDTH=9 HEIGHT=19 TITLE='rh' ALIGN=TOP>";
  althtmldef "rh" as '<FONT COLOR="#0000FF"><I>&rho;</I></FONT>';
  latexdef "rh" as "\rho";
htmldef "mu" as "<IMG SRC='_mu.gif' WIDTH=10 HEIGHT=19 TITLE='mu' ALIGN=TOP>";
  althtmldef "mu" as '<FONT COLOR="#0000FF"><I>&mu;</I></FONT>';
  latexdef "mu" as "\rho";
htmldef "la" as
    "<IMG SRC='_lambda.gif' WIDTH=9 HEIGHT=19 TITLE='la' ALIGN=TOP>";
  althtmldef "la" as '<FONT COLOR="#0000FF"><I>&lambda;</I></FONT>';
  latexdef "la" as "\rho";
htmldef "ka" as
    "<IMG SRC='_kappa.gif' WIDTH=9 HEIGHT=19 TITLE='ka' ALIGN=TOP>";
  althtmldef "ka" as '<FONT COLOR="#0000FF"><I>&kappa;</I></FONT>';
  latexdef "ka" as "\rho";
htmldef "<->" as " <IMG SRC='leftrightarrow.gif' WIDTH=15 HEIGHT=19 " +
    "TITLE='&lt;-&gt;' ALIGN=TOP> ";
  althtmldef "<->" as ' &harr; ';
  latexdef "<->" as "\leftrightarrow";
htmldef "\/" as
     " <IMG SRC='vee.gif' WIDTH=11 HEIGHT=19 TITLE='\/' ALIGN=TOP> ";
  althtmldef "\/" as ' <FONT FACE=sans-serif> &or;</FONT> ' ;
    /* althtmldef "\/" as ' <FONT FACE=sans-serif>&#8897;</FONT> ' ; */
    /* was &or; - changed to match font of &and; replacement */
    /* Changed back 6-Mar-2012 NM */
  latexdef "\/" as "\vee";
htmldef "/\" as
    " <IMG SRC='wedge.gif' WIDTH=11 HEIGHT=19 TITLE='/\' ALIGN=TOP> ";
  althtmldef "/\" as ' <FONT FACE=sans-serif>&and;</FONT> ';
    /* althtmldef "/\" as ' <FONT FACE=sans-serif>&#8896;</FONT> '; */
    /* was &and; which is circle in Mozilla on WinXP Pro (but not Home) */
    /* Changed back 6-Mar-2012 NM */
  latexdef "/\" as "\wedge";
htmldef "-/\" as
    " <IMG SRC='barwedge.gif' WIDTH=9 HEIGHT=19 TITLE='-/\' ALIGN=TOP> ";
  althtmldef "-/\" as ' <FONT FACE=sans-serif>&#8892;</FONT> ';
    /*althtmldef "-/\" as " &#8892; "; */ /* too-high font bug in FF */
    /* barwedge, U022BC, alias ISOAMSB barwed, ['nand'] */
  latexdef "-/\" as "\barwedge";
htmldef "A." as
    "<IMG SRC='forall.gif' WIDTH=10 HEIGHT=19 TITLE='A.' ALIGN=TOP>";
  althtmldef "A." as '<FONT FACE=sans-serif>&forall;</FONT>'; /* &#8704; */
  latexdef "A." as "\forall";
htmldef "set" as
    "<IMG SRC='_set.gif' WIDTH=20 HEIGHT=19 TITLE='set' ALIGN=TOP> ";
  althtmldef "set" as '<FONT COLOR="#808080">set </FONT>';
  latexdef "set" as "{\rm set}";
htmldef "x" as "<IMG SRC='_x.gif' WIDTH=10 HEIGHT=19 TITLE='x' ALIGN=TOP>";
  althtmldef "x" as '<I><FONT COLOR="#FF0000">x</FONT></I>';
  latexdef "x" as "x";
htmldef "y" as "<IMG SRC='_y.gif' WIDTH=9 HEIGHT=19 TITLE='y' ALIGN=TOP>";
  althtmldef "y" as '<I><FONT COLOR="#FF0000">y</FONT></I>';
  latexdef "y" as "y";
htmldef "z" as "<IMG SRC='_z.gif' WIDTH=9 HEIGHT=19 TITLE='z' ALIGN=TOP>";
  althtmldef "z" as '<I><FONT COLOR="#FF0000">z</FONT></I>';
  latexdef "z" as "z";
htmldef "w" as "<IMG SRC='_w.gif' WIDTH=12 HEIGHT=19 TITLE='w' ALIGN=TOP>";
  althtmldef "w" as '<I><FONT COLOR="#FF0000">w</FONT></I>';
  latexdef "w" as "w";
htmldef "v" as "<IMG SRC='_v.gif' WIDTH=9 HEIGHT=19 TITLE='v' ALIGN=TOP>";
  althtmldef "v" as '<I><FONT COLOR="#FF0000">v</FONT></I>';
  latexdef "v" as "v";
htmldef "E." as
    "<IMG SRC='exists.gif' WIDTH=9 HEIGHT=19 TITLE='E.' ALIGN=TOP>";
  althtmldef "E." as '<FONT FACE=sans-serif>&exist;</FONT>'; /* &#8707; */
    /* Without sans-serif, bad in Opera and way too big in FF3 */
  latexdef "E." as "\exists";
htmldef "=" as " <IMG SRC='eq.gif' WIDTH=12 HEIGHT=19 TITLE='=' ALIGN=TOP> ";
  althtmldef "=" as ' = '; /* &equals; */
  latexdef "=" as "=";
htmldef "e." as " <IMG SRC='in.gif' WIDTH=10 HEIGHT=19 TITLE='e.' ALIGN=TOP> ";
  althtmldef "e." as ' <FONT FACE=sans-serif>&isin;</FONT> ';
  latexdef "e." as "\in";
htmldef "[" as "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 TITLE='[' ALIGN=TOP>";
  althtmldef "[" as '['; /* &lsqb; */
  latexdef "[" as "[";
htmldef "/" as
    " <IMG SRC='solidus.gif' WIDTH=6 HEIGHT=19 TITLE='/' ALIGN=TOP> ";
  althtmldef "/" as ' / '; /* &sol; */
  latexdef "/" as "/";
htmldef "]" as "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 TITLE=']' ALIGN=TOP>";
  althtmldef "]" as ']'; /* &rsqb; */
  latexdef "]" as "]";
htmldef "u" as "<IMG SRC='_u.gif' WIDTH=10 HEIGHT=19 TITLE='u' ALIGN=TOP>";
  althtmldef "u" as '<I><FONT COLOR="#FF0000">u</FONT></I>';
  latexdef "u" as "u";
htmldef "f" as "<IMG SRC='_f.gif' WIDTH=9 HEIGHT=19 TITLE='f' ALIGN=TOP>";
  althtmldef "f" as '<I><FONT COLOR="#FF0000">f</FONT></I>';
  latexdef "f" as "f";
htmldef "g" as "<IMG SRC='_g.gif' WIDTH=9 HEIGHT=19 TITLE='g' ALIGN=TOP>";
  althtmldef "g" as '<I><FONT COLOR="#FF0000">g</FONT></I>';
  latexdef "g" as "g";
htmldef "E!" as "<IMG SRC='_e1.gif' WIDTH=12 HEIGHT=19 TITLE='E!' ALIGN=TOP>";
  althtmldef "E!" as '<FONT FACE=sans-serif>&exist;!</FONT>';
  latexdef "E!" as "\exists{!}";
htmldef "E*" as "<IMG SRC='_em1.gif' WIDTH=15 HEIGHT=19 TITLE='E*' ALIGN=TOP>";
  althtmldef "E*" as '<FONT FACE=sans-serif>&exist;*</FONT>';
  latexdef "E*" as "\exists^\ast";

/* "~P" was deleted from above section in set.mm. */
/* The ones below should have been in the above section in set.mm. */
htmldef "class" as
    "<IMG SRC='_class.gif' WIDTH=32 HEIGHT=19 TITLE='class' ALIGN=TOP> ";
  althtmldef "class" as '<FONT COLOR="#808080">class </FONT>';
  latexdef "class" as "{\rm class}";
htmldef "A" as "<IMG SRC='_ca.gif' WIDTH=11 HEIGHT=19 TITLE='A' ALIGN=TOP>";
  althtmldef "A" as '<I><FONT COLOR="#CC33CC">A</FONT></I>';
  latexdef "A" as "A";
htmldef "B" as "<IMG SRC='_cb.gif' WIDTH=12 HEIGHT=19 TITLE='B' ALIGN=TOP>";
  althtmldef "B" as '<I><FONT COLOR="#CC33CC">B</FONT></I>';
  latexdef "B" as "B";
htmldef "T." as
    " <IMG SRC='top.gif' WIDTH=11 HEIGHT=19 TITLE='T.' ALIGN=TOP> ";
  althtmldef "T." as ' &#x22A4; ';
  latexdef "T." as "\top";
htmldef "F." as
    " <IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 TITLE='F.' ALIGN=TOP> ";
  althtmldef "F." as ' &perp; ';
  latexdef "F." as "\bot";

/* End of typesetting definition section */

$)

