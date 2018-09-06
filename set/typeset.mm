
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

/* Note that the ALT= fields in htmldefs should be preceded by a space.  This
   ensures that a screen copy from the web page will have a space between
   symbols. */
/* Math font table with XITS and LaTeX defs:
   http://meeting.contextgarden.net/2011/talks/day3_05_ulrik_opentype/Samples/
           unimath-symbols.pdf */


/******* Web page format settings *******/

/* Custom CSS for Unicode fonts */
/* The woff font file was obtained from
   http://fred-wang.github.io/MathFonts/XITS/xits-math.woff 28-Aug-2015 */
htmlcss '<STYLE TYPE="text/css">\n' +
    '<!--\n' +
    '  .set { color: red; }\n' +
    '  .wff { color: blue; }\n' +
    '  .class { color: #C3C; }\n' +
    '  .symvar { border-bottom:1px dotted;color:#C3C}\n' +
    '  .typecode { color: gray }\n' +
    '  .hidden { color: gray }\n' +
    '  @font-face {\n' +
    '    font-family: XITSMath-Regular;\n' +
    '    src: url(xits-math.woff);\n' +
    '  }\n' +
    '  .math { font-family: XITSMath-Regular }\n' +
    '-->\n' +
    '</STYLE>\n' +
    '<LINK href="mmset.css" title="mmset"\n' +
    '    rel="stylesheet" type="text/css">\n' +
    '<LINK href="mmsetalt.css" title="mmsetalt"\n' +
    '    rel="alternate stylesheet" type="text/css">';

/* Tag(s) for the main SPAN surrounding all Unicode math */
htmlfont 'CLASS=math';

/* Page title, home page link */
htmltitle "Metamath Proof Explorer";
htmlhome '<A HREF="mmset.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="mm.gif" BORDER=0 ALT='  +
    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE STYLE="margin-bottom:0px">' +
    'Home</FONT></A>';
/* Optional file where bibliographic references are kept */
/* If specified, e.g. "mmset.html", Metamath will hyperlink all strings of the
   form "[rrr]" (where "rrr" has no whitespace) to "mmset.html#rrr" */
/* A warning will be given if the file "mmset.html" with the bibliographical
   references is not present.  It is read in order to check existence of
   the references. */
htmlbibliography "mmset.html";

/* Page title, home page link */
/* These are the variables used for the Hilbert Space extension to
   set.mm. */
exthtmltitle "Hilbert Space Explorer";
exthtmlhome '<A HREF="mmhil.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="atomic.gif" BORDER=0 ALT='  +
    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE STYLE="margin-bottom:0px">' +
    'Home</FONT></A>';
/* The variable "exthtmllabel" means that all states including
   and after this label should use the "ext..." variables. */
exthtmllabel "chil";
/* A warning will be given if the file with the bibliographical references
   is not present. */
exthtmlbibliography "mmhil.html";

/* Variable color key at the bottom of each proof table */
htmlvarcolor '<SPAN CLASS=wff STYLE="color:blue;font-style:normal">wff</SPAN> '
    + '<SPAN CLASS=set STYLE="color:red;font-style:normal">set</SPAN> '
    + '<SPAN CLASS=class STYLE="color:#C3C;font-style:normal">class</SPAN>';

/* GIF and Unicode HTML directories - these are used for the GIF version to
   crosslink to the Unicode version and vice-versa */
htmldir "../mpegif/";
althtmldir "../mpeuni/";


/******* Symbol definitions *******/

htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT=' (' TITLE='('>";
  althtmldef "(" as "(";
  latexdef "(" as "(";
htmldef ")" as "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=' )' TITLE=')'>";
  althtmldef ")" as ")";
  latexdef ")" as ")";
htmldef "->" as
    " <IMG SRC='to.gif' WIDTH=15 HEIGHT=19 ALT=' -&gt;' TITLE='-&gt;'> ";
  althtmldef "->" as ' &rarr; ';
  latexdef "->" as "\rightarrow";
htmldef "-." as
    "<IMG SRC='lnot.gif' WIDTH=10 HEIGHT=19 ALT=' -.' TITLE='-.'> ";
  althtmldef "-." as '&not; ';
  latexdef "-." as "\lnot";
htmldef "wff" as
    "<IMG SRC='_wff.gif' WIDTH=24 HEIGHT=19 ALT=' wff' TITLE='wff'> ";
  althtmldef "wff" as
    '<SPAN CLASS=typecode STYLE="color:gray">wff </SPAN>'; /* was #00CC00 */
  latexdef "wff" as "{\rm wff}";
htmldef "|-" as
    "<IMG SRC='_vdash.gif' WIDTH=10 HEIGHT=19 ALT=' |-' TITLE='|-'> ";
  althtmldef "|-" as
    '<SPAN CLASS=hidden STYLE="color:gray">&#8866; </SPAN>'; /* &vdash; */
    /* Without sans-serif, way too big in FF3 */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|-" as "\vdash";
htmldef "ph" as
    "<IMG SRC='_varphi.gif' WIDTH=11 HEIGHT=19 ALT=' ph' TITLE='ph'>";
  /* althtmldef "ph" as '<FONT COLOR="#0000FF">&#x1D711;</SPAN>'; */
  althtmldef "ph" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;</SPAN>';
  latexdef "ph" as "\varphi";
htmldef "ps" as "<IMG SRC='_psi.gif' WIDTH=12 HEIGHT=19 ALT=' ps' TITLE='ps'>";
  althtmldef "ps" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;</SPAN>';
  latexdef "ps" as "\psi";
htmldef "ch" as "<IMG SRC='_chi.gif' WIDTH=12 HEIGHT=19 ALT=' ch' TITLE='ch'>";
  althtmldef "ch" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;</SPAN>';
  latexdef "ch" as "\chi";
htmldef "th" as
    "<IMG SRC='_theta.gif' WIDTH=8 HEIGHT=19 ALT=' th' TITLE='th'>";
  althtmldef "th" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;</SPAN>';
  latexdef "th" as "\theta";
htmldef "ta" as "<IMG SRC='_tau.gif' WIDTH=10 HEIGHT=19 ALT=' ta' TITLE='ta'>";
  althtmldef "ta" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;</SPAN>';
  latexdef "ta" as "\tau";
htmldef "et" as "<IMG SRC='_eta.gif' WIDTH=9 HEIGHT=19 ALT=' et' TITLE='et'>";
  althtmldef "et" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;</SPAN>';
  latexdef "et" as "\eta";
htmldef "ze" as "<IMG SRC='_zeta.gif' WIDTH=9 HEIGHT=19 ALT=' ze' TITLE='ze'>";
  althtmldef "ze" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;</SPAN>';
  latexdef "ze" as "\zeta";
htmldef "si" as
    "<IMG SRC='_sigma.gif' WIDTH=10 HEIGHT=19 ALT=' si' TITLE='si'>";
  althtmldef "si" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;</SPAN>';
  latexdef "si" as "\sigma";
htmldef "rh" as "<IMG SRC='_rho.gif' WIDTH=9 HEIGHT=19 ALT=' rh' TITLE='rh'>";
  althtmldef "rh" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;</SPAN>';
  latexdef "rh" as "\rho";
htmldef "mu" as "<IMG SRC='_mu.gif' WIDTH=10 HEIGHT=19 ALT=' mu' TITLE='mu'>";
  althtmldef "mu" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D707;</SPAN>';
  latexdef "mu" as "\mu";
htmldef "la" as
    "<IMG SRC='_lambda.gif' WIDTH=9 HEIGHT=19 ALT=' la' TITLE='la'>";
  althtmldef "la" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D706;</SPAN>';
  latexdef "la" as "\lambda";
htmldef "ka" as
    "<IMG SRC='_kappa.gif' WIDTH=9 HEIGHT=19 ALT=' ka' TITLE='ka'>";
  althtmldef "ka" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D705;</SPAN>';
  latexdef "ka" as "\kappa";
htmldef "<->" as " <IMG SRC='leftrightarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' &lt;-&gt;' TITLE='&lt;-&gt;'> ";
  althtmldef "<->" as ' &harr; ';
  latexdef "<->" as "\leftrightarrow";
htmldef "\/" as
     " <IMG SRC='vee.gif' WIDTH=11 HEIGHT=19 ALT=' \/' TITLE='\/'> ";
  althtmldef "\/" as ' &or; ' ;
    /* althtmldef "\/" as ' <FONT FACE=sans-serif>&#8897;</FONT> ' ; */
    /* was &or; - changed to match font of &and; replacement */
    /* Changed back 6-Mar-2012 NM */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/" as "\vee";
htmldef "/\" as
    " <IMG SRC='wedge.gif' WIDTH=11 HEIGHT=19 ALT=' /\' TITLE='/\'> ";
  althtmldef "/\" as ' &and; ';
    /* althtmldef "/\" as ' <FONT FACE=sans-serif>&#8896;</FONT> '; */
    /* was &and; which is circle in Mozilla on WinXP Pro (but not Home) */
    /* Changed back 6-Mar-2012 NM */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "/\" as "\wedge";
htmldef "-/\" as
    " <IMG SRC='barwedge.gif' WIDTH=9 HEIGHT=19 ALT=' -/\' TITLE='-/\'> ";
  althtmldef "-/\" as ' &#8892; ';
    /*althtmldef "-/\" as " &#8892; "; */ /* too-high font bug in FF */
    /* barwedge, U022BC, alias ISOAMSB barwed, ['nand'] */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "-/\" as "\barwedge";
htmldef "\/_" as
    " <IMG SRC='veebar.gif' WIDTH=9 HEIGHT=19 ALT=' \/_' TITLE='\/_'> ";
  althtmldef "\/_" as " &#8891; ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/_" as "\veebar";
htmldef "T." as
    " <IMG SRC='top.gif' WIDTH=11 HEIGHT=19 ALT=' T.' TITLE='T.'> ";
  althtmldef "T." as ' &#x22A4; ';
  latexdef "T." as "\top";
htmldef "F." as
    " <IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT=' F.' TITLE='F.'> ";
  althtmldef "F." as ' &perp; ';
  latexdef "F." as "\bot";
htmldef "hadd" as "hadd";
  althtmldef "hadd" as "hadd";
  latexdef "hadd" as "\mbox{hadd}";
htmldef "cadd" as "cadd";
  althtmldef "cadd" as "cadd";
  latexdef "cadd" as "\mbox{cadd}";
htmldef "A." as
    "<IMG SRC='forall.gif' WIDTH=10 HEIGHT=19 ALT=' A.' TITLE='A.'>";
  althtmldef "A." as '&forall;'; /* &#8704; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "A." as "\forall";
htmldef "set" as
    "<IMG SRC='_set.gif' WIDTH=20 HEIGHT=19 ALT=' set' TITLE='set'> ";
  althtmldef "set" as '<SPAN CLASS=typecode STYLE="color:gray">set </SPAN>';
  latexdef "set" as "{\rm set}";
htmldef "x" as "<IMG SRC='_x.gif' WIDTH=10 HEIGHT=19 ALT=' x' TITLE='x'>";
  /* http://www.unicode.org/charts/PDF/U1D400.pdf has math italic Unicode */
  althtmldef "x" as '<SPAN CLASS=set STYLE="color:red">&#x1D465;</SPAN>';
  latexdef "x" as "x";
htmldef "y" as "<IMG SRC='_y.gif' WIDTH=9 HEIGHT=19 ALT=' y' TITLE='y'>";
  althtmldef "y" as '<SPAN CLASS=set STYLE="color:red">&#x1D466;</SPAN>';
  latexdef "y" as "y";
htmldef "z" as "<IMG SRC='_z.gif' WIDTH=9 HEIGHT=19 ALT=' z' TITLE='z'>";
  althtmldef "z" as '<SPAN CLASS=set STYLE="color:red">&#x1D467;</SPAN>';
  latexdef "z" as "z";
htmldef "w" as "<IMG SRC='_w.gif' WIDTH=12 HEIGHT=19 ALT=' w' TITLE='w'>";
  althtmldef "w" as '<SPAN CLASS=set STYLE="color:red">&#x1D464;</SPAN>';
  latexdef "w" as "w";
htmldef "v" as "<IMG SRC='_v.gif' WIDTH=9 HEIGHT=19 ALT=' v' TITLE='v'>";
  althtmldef "v" as '<SPAN CLASS=set STYLE="color:red">&#x1D463;</SPAN>';
  latexdef "v" as "v";
htmldef "u" as "<IMG SRC='_u.gif' WIDTH=10 HEIGHT=19 ALT=' u' TITLE='u'>";
  althtmldef "u" as '<SPAN CLASS=set STYLE="color:red">&#x1D462;</SPAN>';
  latexdef "u" as "u";
htmldef "t" as "<IMG SRC='_t.gif' WIDTH=7 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "t" as '<SPAN CLASS=set STYLE="color:red">&#x1D461;</SPAN>';
  latexdef "t" as "t";
htmldef "E." as
    "<IMG SRC='exists.gif' WIDTH=9 HEIGHT=19 ALT=' E.' TITLE='E.'>";
  althtmldef "E." as '&exist;'; /* &#8707; */
    /* Without sans-serif, bad in Opera and way too big in FF3 */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "E." as "\exists";
htmldef "F/" as
    "<IMG SRC='finv.gif' WIDTH=9 HEIGHT=19 ALT=' F/' TITLE='F/'>";
  althtmldef "F/" as "&#8498;";
  latexdef "F/" as "\Finv";
htmldef "class" as
    "<IMG SRC='_class.gif' WIDTH=32 HEIGHT=19 ALT=' class' TITLE='class'> ";
  althtmldef "class" as
    '<SPAN CLASS=typecode STYLE="color:gray">class </SPAN>';
  latexdef "class" as "{\rm class}";
htmldef "=" as " <IMG SRC='eq.gif' WIDTH=12 HEIGHT=19 ALT=' =' TITLE='='> ";
  althtmldef "=" as ' = '; /* &equals; */
  latexdef "=" as "=";
htmldef "e." as " <IMG SRC='in.gif' WIDTH=10 HEIGHT=19 ALT=' e.' TITLE='e.'> ";
  althtmldef "e." as ' &isin; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "e." as "\in";
htmldef "[" as "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 ALT=' [' TITLE='['>";
  althtmldef "[" as '['; /* &lsqb; */
  latexdef "[" as "[";
htmldef "/" as
    " <IMG SRC='solidus.gif' WIDTH=6 HEIGHT=19 ALT=' /' TITLE='/'> ";
  althtmldef "/" as ' / '; /* &sol; */
  latexdef "/" as "/";
htmldef "]" as "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 ALT=' ]' TITLE=']'>";
  althtmldef "]" as ']'; /* &rsqb; */
  latexdef "]" as "]";
htmldef "E!" as "<IMG SRC='_e1.gif' WIDTH=12 HEIGHT=19 ALT=' E!' TITLE='E!'>";
  althtmldef "E!" as '&exist;!';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "E!" as "\exists{!}";
htmldef "E*" as "<IMG SRC='_em1.gif' WIDTH=15 HEIGHT=19 ALT=' E*' TITLE='E*'>";
  althtmldef "E*" as '&exist;*';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "E*" as "\exists^\ast";
htmldef "{" as "<IMG SRC='lbrace.gif' WIDTH=6 HEIGHT=19 ALT=' {' TITLE='{'>";
  althtmldef "{" as '{'; /* &lcub; */
  latexdef "{" as "\{";
htmldef "|" as " <IMG SRC='vert.gif' WIDTH=3 HEIGHT=19 ALT=' |' TITLE='|'> ";
  althtmldef "|" as ' &#8739; '; /* &vertbar; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|" as "|";
htmldef "}" as "<IMG SRC='rbrace.gif' WIDTH=6 HEIGHT=19 ALT=' }' TITLE='}'>";
  althtmldef "}" as '}'; /* &rcub; */
  latexdef "}" as "\}";
htmldef "F/_" as
    "<IMG SRC='_finvbar.gif' WIDTH=9 HEIGHT=19 ALT=' F/_' TITLE='F/_'>";
  althtmldef "F/_" as "<U>&#8498;</U>";
  latexdef "F/_" as "\underline{\Finv}";
htmldef "CondEq" as "CondEq";
  althtmldef "CondEq" as "CondEq";
  latexdef "CondEq" as "\mbox{CondEq}";
htmldef "./\" as
    " <IMG SRC='_.wedge.gif' WIDTH=11 HEIGHT=19 ALT=' ./\' TITLE='./\'> ";
  althtmldef "./\" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&and;</SPAN> ';
  latexdef "./\" as "\wedge";
htmldef ".\/" as
    " <IMG SRC='_.vee.gif' WIDTH=11 HEIGHT=19 ALT=' .\/' TITLE='.\/'> ";
  althtmldef ".\/" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&or;</SPAN> ';
  latexdef ".\/" as "\vee";
htmldef ".<_" as
    " <IMG SRC='_.le.gif' WIDTH=11 HEIGHT=19 ALT=' .&lt;_' TITLE='.&lt;_'> ";
  althtmldef ".<_" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&le;</SPAN> ';
  latexdef ".<_" as "\le";
htmldef ".<" as     /* Symbol as variable */
    " <IMG SRC='_.lt.gif' WIDTH=11 HEIGHT=19 ALT=' .&lt;' TITLE='.&lt;'> ";
  althtmldef ".<" as
    /* This is how to put a dotted box around the symbol: */
    /* border means box around symbol; border-bottom underlines symbol */
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&lt;</SPAN> ';
    /* Todo: can this STYLE sequence be done with a CLASS? */
    /* Move the underline down 3px so it isn't too close to symbol */
    /*
    ' <SPAN STYLE="vertical-align:-3px">' +
    '<SPAN CLASS=symvar STYLE="text-decoration:underline dotted;color:#C3C">' +
    '<SPAN STYLE="vertical-align:3px">&lt;</SPAN></SPAN></SPAN> ';
    */
  latexdef ".<" as "<";
htmldef ".+" as
    " <IMG SRC='_.plus.gif' WIDTH=13 HEIGHT=19 ALT=' .+' TITLE='.+'> ";
  althtmldef ".+" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '+</SPAN> ';
  latexdef ".+" as "+";
htmldef ".-" as
    " <IMG SRC='_.minus.gif' WIDTH=11 HEIGHT=19 ALT=' .-' TITLE='.-'> ";
  althtmldef ".-" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&minus;</SPAN> ';
  latexdef ".-" as "-";
htmldef ".X." as
    " <IMG SRC='_.times.gif' WIDTH=9 HEIGHT=19 ALT=' .X.' TITLE='.X.'> ";
  althtmldef ".X." as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&times;</SPAN> ';
  latexdef ".X." as "\times";
htmldef "./" as
    " <IMG SRC='_.solidus.gif' WIDTH=8 HEIGHT=19 ALT=' ./' TITLE='./'> ";
  althtmldef "./" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '/</SPAN> ';
  latexdef "./" as "/";
htmldef ".^" as
    " <IMG SRC='_.uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' .^' TITLE='.^'> ";
  althtmldef ".^" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&uarr;</SPAN> ';
  latexdef ".^" as "\uparrow";
htmldef ".0." as
    " <IMG SRC='_.0.gif' WIDTH=8 HEIGHT=19 ALT=' .0.' TITLE='.0.'> ";
  althtmldef ".0." as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '0</SPAN> ';
  latexdef ".0." as "0";
htmldef ".1." as
    " <IMG SRC='_.1.gif' WIDTH=7 HEIGHT=19 ALT=' .1.' TITLE='.1.'> ";
  althtmldef ".1." as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '1</SPAN> ';
  latexdef ".1." as "1";
htmldef ".||" as
    " <IMG SRC='_.parallel.gif' WIDTH=5 HEIGHT=19 ALT=' .||' TITLE='.||'> ";
  althtmldef ".||" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#8741;</SPAN> ';
  latexdef ".||" as "\parallel";
htmldef ".~" as
    " <IMG SRC='_.sim.gif' WIDTH=13 HEIGHT=19 ALT=' .~' TITLE='.~'> ";
  althtmldef ".~" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x223C;</SPAN> ';
  latexdef ".~" as "\sim";
htmldef "._|_" as
    " <IMG SRC='_.perp.gif' WIDTH=11 HEIGHT=19 ALT=' ._|_' TITLE='._|_'> ";
  althtmldef "._|_" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#8869;</SPAN> ';
  latexdef "._|_" as "\perp";
htmldef ".+^" as
    " <IMG SRC='_.plushat.gif' WIDTH=11 HEIGHT=19 ALT=' .+^' TITLE='.+^'> ";
  althtmldef ".+^" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x2A23;</SPAN> ';       /* &plusacir; */
  latexdef ".+^" as "\hat{+}";
htmldef ".+b" as
    " <IMG SRC='_.plusb.gif' WIDTH=14 HEIGHT=19 ALT=' .+b' TITLE='.+b'> ";
  althtmldef ".+b" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x271A;</SPAN> ';
  latexdef ".+b" as "\boldsymbol{+}";
htmldef ".(+)" as
    " <IMG SRC='_.oplus.gif' WIDTH=13 HEIGHT=19 ALT=' .(+)' TITLE='.(+)'> ";
  althtmldef ".(+)" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x2295;</SPAN> ';
  latexdef ".(+)" as "\oplus";
htmldef ".*" as
    " <IMG SRC='_.ast.gif' WIDTH=7 HEIGHT=19 ALT=' .*' TITLE='.*'> ";
  althtmldef ".*" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&lowast;</SPAN> ';
  latexdef ".*" as "\ast";
htmldef ".x." as
    " <IMG SRC='_.cdot.gif' WIDTH=4 HEIGHT=19 ALT=' .x.' TITLE='.x.'> ";
  althtmldef ".x." as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&middot;</SPAN> ';
  latexdef ".x." as "\cdot";
htmldef ".xb" as
    " <IMG SRC='_.bullet.gif' WIDTH=8 HEIGHT=19 ALT=' .xb' TITLE='.xb'> ";
  althtmldef ".xb" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x2219;</SPAN> ';
  latexdef ".xb" as "\bullet";
htmldef ".," as
    " <IMG SRC='_.comma.gif' WIDTH=4 HEIGHT=19 ALT=' .,' TITLE='.,'> ";
  althtmldef ".," as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    ',</SPAN> ';
  latexdef ".," as ",";
htmldef ".(x)" as
    " <IMG SRC='_.otimes.gif' WIDTH=13 HEIGHT=19 ALT=' .(x)' TITLE='.(x)'> ";
  althtmldef ".(x)" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x2297;</SPAN> ';
  latexdef ".(x)" as "\otimes";
htmldef ".0b" as
    " <IMG SRC='_.bf0.gif' WIDTH=9 HEIGHT=19 ALT=' .0b' TITLE='.0b'> ";
  althtmldef ".0b" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x1D7CE</SPAN> ';
  latexdef ".0b" as "\mbox{\boldmath$0$}";
htmldef "A" as "<IMG SRC='_ca.gif' WIDTH=11 HEIGHT=19 ALT=' A' TITLE='A'>";
  althtmldef "A" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;</SPAN>';
  latexdef "A" as "A";
htmldef "B" as "<IMG SRC='_cb.gif' WIDTH=12 HEIGHT=19 ALT=' B' TITLE='B'>";
  althtmldef "B" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;</SPAN>';
  latexdef "B" as "B";
htmldef "C" as "<IMG SRC='_cc.gif' WIDTH=12 HEIGHT=19 ALT=' C' TITLE='C'>";
  althtmldef "C" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;</SPAN>';
  latexdef "C" as "C";
htmldef "D" as "<IMG SRC='_cd.gif' WIDTH=12 HEIGHT=19 ALT=' D' TITLE='D'>";
  althtmldef "D" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;</SPAN>';
  latexdef "D" as "D";
htmldef "P" as "<IMG SRC='_cp.gif' WIDTH=12 HEIGHT=19 ALT=' P' TITLE='P'>";
  althtmldef "P" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;</SPAN>';
  latexdef "P" as "P";
htmldef "Q" as "<IMG SRC='_cq.gif' WIDTH=12 HEIGHT=19 ALT=' Q' TITLE='Q'>";
  althtmldef "Q" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;</SPAN>';
  latexdef "Q" as "Q";
htmldef "R" as "<IMG SRC='_cr.gif' WIDTH=12 HEIGHT=19 ALT=' R' TITLE='R'>";
  althtmldef "R" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;</SPAN>';
  latexdef "R" as "R";
htmldef "S" as "<IMG SRC='_cs.gif' WIDTH=11 HEIGHT=19 ALT=' S' TITLE='S'>";
  althtmldef "S" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;</SPAN>';
  latexdef "S" as "S";
htmldef "T" as "<IMG SRC='_ct.gif' WIDTH=12 HEIGHT=19 ALT=' T' TITLE='T'>";
  althtmldef "T" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;</SPAN>';
  latexdef "T" as "T";
htmldef "U" as "<IMG SRC='_cu.gif' WIDTH=12 HEIGHT=19 ALT=' U' TITLE='U'>";
  althtmldef "U" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;</SPAN>';
  latexdef "U" as "U";
htmldef "e" as "<IMG SRC='_e.gif' WIDTH=8 HEIGHT=19 ALT=' e' TITLE='e'>";
  althtmldef "e" as '<SPAN CLASS=set STYLE="color:red">&#x1D452;</SPAN>';
  latexdef "e" as "e";
htmldef "f" as "<IMG SRC='_f.gif' WIDTH=9 HEIGHT=19 ALT=' f' TITLE='f'>";
  althtmldef "f" as '<SPAN CLASS=set STYLE="color:red">&#x1D453;</SPAN>';
  latexdef "f" as "f";
htmldef "g" as "<IMG SRC='_g.gif' WIDTH=9 HEIGHT=19 ALT=' g' TITLE='g'>";
  althtmldef "g" as '<SPAN CLASS=set STYLE="color:red">&#x1D454;</SPAN>';
  latexdef "g" as "g";
htmldef "h" as "<IMG SRC='_h.gif' WIDTH=10 HEIGHT=19 ALT=' h' TITLE='h'>";
  althtmldef "h" as '<SPAN CLASS=set STYLE="color:red">&#x210E;</SPAN>';
  latexdef "h" as "h";
htmldef "i" as "<IMG SRC='_i.gif' WIDTH=6 HEIGHT=19 ALT=' i' TITLE='i'>";
  althtmldef "i" as '<SPAN CLASS=set STYLE="color:red">&#x1D456;</SPAN>';
  latexdef "i" as "i";
htmldef "j" as "<IMG SRC='_j.gif' WIDTH=7 HEIGHT=19 ALT=' j' TITLE='j'>";
  althtmldef "j" as '<SPAN CLASS=set STYLE="color:red">&#x1D457;</SPAN>';
  latexdef "j" as "j";
htmldef "k" as "<IMG SRC='_k.gif' WIDTH=9 HEIGHT=19 ALT=' k' TITLE='k'>";
  althtmldef "k" as '<SPAN CLASS=set STYLE="color:red">&#x1D458;</SPAN>';
  latexdef "k" as "k";
htmldef "m" as "<IMG SRC='_m.gif' WIDTH=14 HEIGHT=19 ALT=' m' TITLE='m'>";
  althtmldef "m" as '<SPAN CLASS=set STYLE="color:red">&#x1D45A;</SPAN>';
  latexdef "m" as "m";
htmldef "n" as "<IMG SRC='_n.gif' WIDTH=10 HEIGHT=19 ALT=' n' TITLE='n'>";
  althtmldef "n" as '<SPAN CLASS=set STYLE="color:red">&#x1D45B;</SPAN>';
  latexdef "n" as "n";
htmldef "o" as "<IMG SRC='_o.gif' WIDTH=8 HEIGHT=19 ALT=' o' TITLE='o'>";
  althtmldef "o" as '<SPAN CLASS=set STYLE="color:red">&#x1D45C;</SPAN>';
  latexdef "o" as "o";
htmldef "E" as "<IMG SRC='_ce.gif' WIDTH=13 HEIGHT=19 ALT=' E' TITLE='E'>";
  althtmldef "E" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;</SPAN>';
  latexdef "E" as "E";
htmldef "F" as "<IMG SRC='_cf.gif' WIDTH=13 HEIGHT=19 ALT=' F' TITLE='F'>";
  althtmldef "F" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;</SPAN>';
  latexdef "F" as "F";
htmldef "G" as "<IMG SRC='_cg.gif' WIDTH=12 HEIGHT=19 ALT=' G' TITLE='G'>";
  althtmldef "G" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;</SPAN>';
  latexdef "G" as "G";
htmldef "H" as "<IMG SRC='_ch.gif' WIDTH=14 HEIGHT=19 ALT=' H' TITLE='H'>";
  althtmldef "H" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;</SPAN>';
  latexdef "H" as "H";
htmldef "I" as "<IMG SRC='_ci.gif' WIDTH=8 HEIGHT=19 ALT=' I' TITLE='I'>";
  althtmldef "I" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;</SPAN>';
  latexdef "I" as "I";
htmldef "J" as "<IMG SRC='_cj.gif' WIDTH=10 HEIGHT=19 ALT=' J' TITLE='J'>";
  althtmldef "J" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;</SPAN>';
  latexdef "J" as "J";
htmldef "K" as "<IMG SRC='_ck.gif' WIDTH=14 HEIGHT=19 ALT=' K' TITLE='K'>";
  althtmldef "K" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;</SPAN>';
  latexdef "K" as "K";
htmldef "L" as "<IMG SRC='_cl.gif' WIDTH=10 HEIGHT=19 ALT=' L' TITLE='L'>";
  althtmldef "L" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;</SPAN>';
  latexdef "L" as "L";
htmldef "M" as "<IMG SRC='_cm.gif' WIDTH=15 HEIGHT=19 ALT=' M' TITLE='M'>";
  althtmldef "M" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;</SPAN>';
  latexdef "M" as "M";
htmldef "N" as "<IMG SRC='_cn.gif' WIDTH=14 HEIGHT=19 ALT=' N' TITLE='N'>";
  althtmldef "N" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;</SPAN>';
  latexdef "N" as "N";
htmldef "V" as "<IMG SRC='_cv.gif' WIDTH=12 HEIGHT=19 ALT=' V' TITLE='V'>";
  althtmldef "V" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;</SPAN>';
  latexdef "V" as "V";
htmldef "W" as "<IMG SRC='_cw.gif' WIDTH=16 HEIGHT=19 ALT=' W' TITLE='W'>";
  althtmldef "W" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;</SPAN>';
  latexdef "W" as "W";
htmldef "X" as "<IMG SRC='_cx.gif' WIDTH=13 HEIGHT=19 ALT=' X' TITLE='X'>";
  althtmldef "X" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;</SPAN>';
  latexdef "X" as "X";
htmldef "Y" as "<IMG SRC='_cy.gif' WIDTH=12 HEIGHT=19 ALT=' Y' TITLE='Y'>";
  althtmldef "Y" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;</SPAN>';
  latexdef "Y" as "Y";
htmldef "Z" as "<IMG SRC='_cz.gif' WIDTH=11 HEIGHT=19 ALT=' Z' TITLE='Z'>";
  althtmldef "Z" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;</SPAN>';
  latexdef "Z" as "Z";
htmldef "O" as "<IMG SRC='_co.gif' WIDTH=12 HEIGHT=19 ALT=' O' TITLE='O'>";
  althtmldef "O" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;</SPAN>';
  latexdef "O" as "O";
htmldef "s" as "<IMG SRC='_s.gif' WIDTH=7 HEIGHT=19 ALT=' s' TITLE='s'>";
  althtmldef "s" as '<SPAN CLASS=set STYLE="color:red">&#x1D460;</SPAN>';
  latexdef "s" as "s";
htmldef "r" as "<IMG SRC='_r.gif' WIDTH=8 HEIGHT=19 ALT=' r' TITLE='r'>";
  althtmldef "r" as '<SPAN CLASS=set STYLE="color:red">&#x1D45F;</SPAN>';
  latexdef "r" as "r";
htmldef "q" as "<IMG SRC='_q.gif' WIDTH=8 HEIGHT=19 ALT=' q' TITLE='q'>";
  althtmldef "q" as '<SPAN CLASS=set STYLE="color:red">&#x1D45E;</SPAN>';
  latexdef "q" as "q";
htmldef "p" as "<IMG SRC='_p.gif' WIDTH=10 HEIGHT=19 ALT=' p' TITLE='p'>";
  althtmldef "p" as '<SPAN CLASS=set STYLE="color:red">&#x1D45D;</SPAN>';
  latexdef "p" as "p";
htmldef "a" as "<IMG SRC='_a.gif' WIDTH=9 HEIGHT=19 ALT=' a' TITLE='a'>";
  althtmldef "a" as '<SPAN CLASS=set STYLE="color:red">&#x1D44E;</SPAN>';
  latexdef "a" as "a";
htmldef "b" as "<IMG SRC='_b.gif' WIDTH=8 HEIGHT=19 ALT=' b' TITLE='b'>";
  althtmldef "b" as '<SPAN CLASS=set STYLE="color:red">&#x1D44F;</SPAN>';
  latexdef "b" as "b";
htmldef "c" as "<IMG SRC='_c.gif' WIDTH=7 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "c" as '<SPAN CLASS=set STYLE="color:red">&#x1D450;</SPAN>';
  latexdef "c" as "c";
htmldef "d" as "<IMG SRC='_d.gif' WIDTH=9 HEIGHT=19 ALT=' d' TITLE='d'>";
  althtmldef "d" as '<SPAN CLASS=set STYLE="color:red">&#x1D451;</SPAN>';
  latexdef "d" as "d";
htmldef "l" as "<IMG SRC='_l.gif' WIDTH=6 HEIGHT=19 ALT=' l' TITLE='l'>";
  althtmldef "l" as '<SPAN CLASS=set STYLE="color:red">&#x1D459;</SPAN>';
  latexdef "l" as "l";
htmldef "=/=" as
    " <IMG SRC='ne.gif' WIDTH=12 HEIGHT=19 ALT=' =/=' TITLE='=/='> ";
  althtmldef "=/=" as ' &ne; ';
  latexdef "=/=" as "\ne";
htmldef "e/" as
    " <IMG SRC='notin.gif' WIDTH=10 HEIGHT=19 ALT=' e/' TITLE='e/'> ";
  althtmldef "e/" as ' &notin; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "e/" as "\notin";
htmldef "_V" as "<IMG SRC='rmcv.gif' WIDTH=10 HEIGHT=19 ALT=' _V' TITLE='_V'>";
  althtmldef "_V" as 'V';
  latexdef "_V" as "{\rm V}";
htmldef "[." as
    "<IMG SRC='_dlbrack.gif' WIDTH=7 HEIGHT=19 ALT=' [.' TITLE='[.'>";
  /* althtmldef "[." as '&#x298F;'; */   /* corner tick */
  /* althtmldef "[." as '[&#803;'; */  /* combining dot below */
  althtmldef "[." as '<B>[</B>'; /* 6-Aug-2018 nm */
  /* \underaccent is in accents package */
  latexdef "[." as "\underaccent{\dot}{[}";
htmldef "]." as
    "<IMG SRC='_drbrack.gif' WIDTH=6 HEIGHT=19 ALT=' ].' TITLE='].'>";
  /* althtmldef "]." as '&#x298E;'; */   /* corner tick */
  /* althtmldef "]." as ']&#803;'; */  /* combining dot below */
  althtmldef "]." as '<B>]</B>'; /* 6-Aug-2018 nm */
  latexdef "]." as "\underaccent{\dot}{]}";
htmldef "[_" as
    "<IMG SRC='_ulbrack.gif' WIDTH=7 HEIGHT=19 ALT=' [_' TITLE='[_'>";
  althtmldef "[_" as '<B>&#x298B;</B>'; /* left sq brack w underbar */
  latexdef "[_" as "\underline{[}";
htmldef "]_" as
    "<IMG SRC='_urbrack.gif' WIDTH=6 HEIGHT=19 ALT=' ]_' TITLE=']_'>";
  althtmldef "]_" as '<B>&#x298C;</B>'; /* right sq brack w underbar */
  latexdef "]_" as "\underline{]}";
htmldef "\" as
    " <IMG SRC='setminus.gif' WIDTH=8 HEIGHT=19 ALT=' \' TITLE='\'> ";
  althtmldef "\" as ' &#8726; '; /* &setmn; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\" as "\setminus";
htmldef "u." as
    " <IMG SRC='cup.gif' WIDTH=10 HEIGHT=19 ALT=' u.' TITLE='u.'> ";
  althtmldef "u." as ' &cup; ';
  latexdef "u." as "\cup";
htmldef "i^i" as
    " <IMG SRC='cap.gif' WIDTH=10 HEIGHT=19 ALT=' i^i' TITLE='i^i'> ";
  althtmldef "i^i" as ' &cap; ';
  latexdef "i^i" as "\cap";
htmldef "C_" as
    " <IMG SRC='subseteq.gif' WIDTH=12 HEIGHT=19 ALT=' C_' TITLE='C_'> ";
  althtmldef "C_" as ' &#8838; '; /* &subE; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "C_" as "\subseteq";
htmldef "C." as
    " <IMG SRC='subset.gif' WIDTH=12 HEIGHT=19 ALT=' C.' TITLE='C.'> ";
  althtmldef "C." as ' &sub; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "C." as "\subset";
htmldef "(/)" as
    "<IMG SRC='varnothing.gif' WIDTH=11 HEIGHT=19 ALT=' (/)' TITLE='(/)'>";
  althtmldef "(/)" as '&empty;';
    /*althtmldef "(/)" as '&empty;';*/ /* =&#8709 */ /* bad in Opera */
    /*althtmldef "(/)" as '&#8960;';*/
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "(/)" as "\varnothing";
htmldef "if" as "<IMG SRC='_if.gif' WIDTH=11 HEIGHT=19 ALT=' if' TITLE='if'>";
  althtmldef "if" as ' if';
  latexdef "if" as "{\rm if}";
htmldef "," as "<IMG SRC='comma.gif' WIDTH=4 HEIGHT=19 ALT=' ,' TITLE=','> ";
  althtmldef "," as ', ';
  latexdef "," as ",";
htmldef "~P" as "<IMG SRC='scrp.gif' WIDTH=16 HEIGHT=19 ALT=' ~P' TITLE='~P'>";
  /* althtmldef "~P" as '<FONT FACE=sans-serif>&weierp;</FONT>'; */
  /* althtmldef "~P" as '&weierp;'; */ /* 2-Jan-2016 reverted sans-serif */
  /* 14-Jan-2016 script P is now available in upper Unicode */
  /* 4-Aug-2016 NM Put space after ~P, needed for e.g. ncanth where it
     overlapped the _V */
  althtmldef "~P" as '&#119979; ';
  latexdef "~P" as "{\cal P}";
htmldef "<." as
    "<IMG SRC='langle.gif' WIDTH=4 HEIGHT=19 ALT=' &lt;.' TITLE='&lt;.'>";
    /* The Unicode below doesn't always work on Firefox and Chrome on Windows,
       so revert to the image above */
  althtmldef "<." as '&lang;'; /* &#9001; */
    /* 2-Jan-2016 restored Unicode; reverted sans-serif */
  latexdef "<." as "\langle";
htmldef ">." as
    "<IMG SRC='rangle.gif' WIDTH=4 HEIGHT=19 ALT=' &gt;.' TITLE='&gt;.'>";
    /* The Unicode below doesn't always work on Firefox and Chrome on Windows,
       so revert to the image above */
  althtmldef ">." as '&rang;'; /* &#9002; */
    /* 2-Jan-2016 restored Unicode; reverted sans-serif */
  latexdef ">." as "\rangle";
htmldef "U." as
    "<IMG SRC='bigcup.gif' WIDTH=13 HEIGHT=19 ALT=' U.' TITLE='U.'>";
  /* 20-Sep-2017 nm Add space after U. in althtmldef to improve "U. ran" */
  althtmldef "U." as '<FONT SIZE="+1">&cup;</FONT> '; /* &xcup; */
    /* xcup does not render, and #8899 renders as a small bold cup, on
       Mozilla 1.7.3 on Windows XP */
    /*althtmldef "U." as '&#8899;';*/ /* &xcup; */
  latexdef "U." as "\bigcup";
htmldef "|^|" as
    "<IMG SRC='bigcap.gif' WIDTH=13 HEIGHT=19 ALT=' |^|' TITLE='|^|'>";
  /* 20-Sep-2017 nm Add space after |^| in althtmldef to improve "|^| ran" */
  althtmldef "|^|" as '<FONT SIZE="+1">&cap;</FONT> '; /* &xcap; */
    /*althtmldef "|^|" as '&#8898;';*/ /* &xcap; */
  latexdef "|^|" as "\bigcap";
htmldef "U_" as
    "<IMG SRC='_cupbar.gif' WIDTH=13 HEIGHT=19 ALT=' U_' TITLE='U_'>";
  /* 20-Sep-2017 nm Add space after U_ in althtmldef to improve "U_ ran" */
  althtmldef "U_" as '<U><FONT SIZE="+1">&cup;</FONT></U> '; /* &xcup; */
  latexdef "U_" as "\underline{\bigcup}";
htmldef "|^|_" as
    "<IMG SRC='_capbar.gif' WIDTH=13 HEIGHT=19 ALT=' |^|_' TITLE='|^|_'>";
  /* 20-Sep-2017 nm Add space after |^|_ in althtmldef to improve "|^|_ ran" */
  althtmldef "|^|_" as '<U><FONT SIZE="+1">&cap;</FONT></U> '; /* &xcap; */
  latexdef "|^|_" as "\underline{\bigcap}";
htmldef "Disj_" as "<u>Disj</u> ";
  althtmldef "Disj_" as "<u>Disj</u> ";
  latexdef "Disj_" as "\operatorname{\underline{Disj}}";
htmldef "|->" as " <IMG SRC='mapsto.gif' WIDTH=15 HEIGHT=19 ALT=' |-&gt;'" +
    " TITLE='|-&gt;'> ";
  althtmldef "|->" as ' &#8614; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|->" as "\mapsto";
htmldef "Tr" as
    "<IMG SRC='_ctr.gif' WIDTH=16 HEIGHT=19 ALT=' Tr' TITLE='Tr'> ";
  althtmldef "Tr" as 'Tr ';
  latexdef "Tr" as "{\rm Tr}";
htmldef "_E" as
    " <IMG SRC='rmce.gif' WIDTH=9 HEIGHT=19 ALT=' _E' TITLE='_E'> ";
  althtmldef "_E" as ' E ';
  latexdef "_E" as "{\rm E}";
htmldef "_I" as
    " <IMG SRC='rmci.gif' WIDTH=4 HEIGHT=19 ALT=' _I' TITLE='_I'> ";
  althtmldef "_I" as ' I ';
  latexdef "_I" as "{\rm I}";
htmldef "Po" as
    " <IMG SRC='_po.gif' WIDTH=16 HEIGHT=19 ALT=' Po' TITLE='Po'> ";
  althtmldef "Po" as ' Po ';
  latexdef "Po" as "{\rm Po}";
htmldef "Or" as
    " <IMG SRC='_or.gif' WIDTH=18 HEIGHT=19 ALT=' Or' TITLE='Or'> ";
  althtmldef "Or" as ' Or ';
  latexdef "Or" as "{\rm Or}";
htmldef "Fr" as
    " <IMG SRC='_fr.gif' WIDTH=15 HEIGHT=19 ALT=' Fr' TITLE='Fr'> ";
  althtmldef "Fr" as ' Fr ';
  latexdef "Fr" as "{\rm Fr}";
htmldef "Se" as ' Se ';
  althtmldef "Se" as ' Se ';
  latexdef "Se" as "{\rm Se}";
htmldef "We" as
    " <IMG SRC='_we.gif' WIDTH=21 HEIGHT=19 ALT=' We' TITLE='We'> ";
  althtmldef "We" as ' We ';
  latexdef "We" as "{\rm We}";
htmldef "Ord" as
    "<IMG SRC='_ord.gif' WIDTH=26 HEIGHT=19 ALT=' Ord' TITLE='Ord'> ";
  althtmldef "Ord" as 'Ord ';
  latexdef "Ord" as "{\rm Ord}";
htmldef "On" as "<IMG SRC='_on.gif' WIDTH=20 HEIGHT=19 ALT=' On' TITLE='On'>";
  althtmldef "On" as 'On';
  latexdef "On" as "{\rm On}";
htmldef "Lim" as
    "<IMG SRC='_lim.gif' WIDTH=26 HEIGHT=19 ALT=' Lim' TITLE='Lim'> ";
  althtmldef "Lim" as 'Lim ';
  latexdef "Lim" as "{\rm Lim}";
htmldef "suc" as
    "<IMG SRC='_suc.gif' WIDTH=22 HEIGHT=19 ALT=' suc' TITLE='suc'> ";
  althtmldef "suc" as 'suc ';
  latexdef "suc" as "{\rm suc}";
htmldef "om" as
    "<IMG SRC='omega.gif' WIDTH=11 HEIGHT=19 ALT=' om' TITLE='om'>";
  /*althtmldef "om" as '&omega;';*/
  althtmldef "om" as '&#x1D714;'; /* math italic omega */
  latexdef "om" as "\omega";
htmldef "X." as
    " <IMG SRC='times.gif' WIDTH=9 HEIGHT=19 ALT=' X.' TITLE='X.'> ";
  althtmldef "X." as ' &times; ';
  latexdef "X." as "\times";
htmldef "`'" as "<IMG SRC='_cnv.gif' WIDTH=10 HEIGHT=19 ALT=" + '"' + " `'" +
    '"' + "TITLE=" + '"' + "`'" + '"' + ">";
  althtmldef "`'" as '<FONT SIZE="-1"><SUP>&#9697;</SUP></FONT>'; /* or 8995 */
  latexdef "`'" as "{}^{\smallsmile}";
htmldef "dom" as
    "<IMG SRC='_dom.gif' WIDTH=26 HEIGHT=19 ALT=' dom' TITLE='dom'> ";
  althtmldef "dom" as 'dom ';
  latexdef "dom" as "{\rm dom}";
htmldef "ran" as
    "<IMG SRC='_ran.gif' WIDTH=22 HEIGHT=19 ALT=' ran' TITLE='ran'> ";
  althtmldef "ran" as 'ran ';
  latexdef "ran" as "{\rm ran}";
htmldef "|`" as " <IMG SRC='restriction.gif' WIDTH=5 HEIGHT=19 ALT=' |`'" +
    " TITLE='|`'> ";
  althtmldef "|`" as ' &#8638; '; /* &uharr; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|`" as "\restriction";
htmldef '"' as "<IMG SRC='backquote.gif' WIDTH=7 HEIGHT=19 ALT=' " + '"' +
    "' TITLE='" + '"' + "'>";
  althtmldef '"' as ' &ldquo; '; /* &#8220; */
  latexdef '"' as "``";
htmldef "o." as
    " <IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' o.' TITLE='o.'> ";
  althtmldef "o." as ' &#8728; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "o." as "\circ";
htmldef "Rel" as
    "<IMG SRC='_rel.gif' WIDTH=22 HEIGHT=19 ALT=' Rel' TITLE='Rel'> ";
  althtmldef "Rel" as 'Rel ';
  latexdef "Rel" as "{\rm Rel}";
htmldef "Fun" as
    "<IMG SRC='_fun.gif' WIDTH=25 HEIGHT=19 ALT=' Fun' TITLE='Fun'> ";
  althtmldef "Fun" as 'Fun ';
  latexdef "Fun" as "{\rm Fun}";
htmldef "Fn" as
    " <IMG SRC='_fn.gif' WIDTH=17 HEIGHT=19 ALT=' Fn' TITLE='Fn'> ";
  althtmldef "Fn" as ' Fn ';
  latexdef "Fn" as "{\rm Fn}";
htmldef ":" as "<IMG SRC='colon.gif' WIDTH=4 HEIGHT=19 ALT=' :' TITLE=':'>";
  althtmldef ":" as ':';
  latexdef ":" as ":";
htmldef "-->" as
  "<IMG SRC='longrightarrow.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' --&gt;' TITLE='--&gt;'>";
  /* althtmldef "-->" as '&ndash;&rarr;'; */
  althtmldef "-->" as '&#x27F6;';
    /* &#xAD;&#x2010;&ndash;&mdash;&minus; (possible symbols test) */
  latexdef "-->" as "\longrightarrow";
htmldef "-1-1->" as "<IMG SRC='onetoone.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' -1-1-&gt;' TITLE='-1-1-&gt;'>";
  althtmldef "-1-1->" as
    '&ndash;<FONT SIZE=-2 FACE=sans-serif>1-1</FONT>&rarr;';
  latexdef "-1-1->" as
    "\raisebox{.5ex}{${\textstyle{\:}_{\mbox{\footnotesize\rm 1" +
    "\tt -\rm 1}}}\atop{\textstyle{" +
    "\longrightarrow}\atop{\textstyle{}^{\mbox{\footnotesize\rm {\ }}}}}$}";
htmldef "-onto->" as
    "<IMG SRC='onto.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' -onto-&gt;' TITLE='-onto-&gt;'>";
  althtmldef "-onto->" as
    '&ndash;<FONT SIZE=-2 FACE=sans-serif>onto</FONT>&rarr;';
  latexdef "-onto->" as
    "\raisebox{.5ex}{${\textstyle{\:}_{\mbox{\footnotesize\rm {\ }}}}" +
    "\atop{\textstyle{" +
    "\longrightarrow}\atop{\textstyle{}^{\mbox{\footnotesize\rm onto}}}}$}";
htmldef "-1-1-onto->" as "<IMG SRC='onetooneonto.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' -1-1-onto-&gt;' TITLE='-1-1-onto-&gt;'>";
  althtmldef "-1-1-onto->" as '&ndash;<FONT SIZE=-2 '
    + 'FACE=sans-serif>1-1</FONT>-<FONT SIZE=-2 '
    + 'FACE=sans-serif>onto</FONT>&rarr;';
  latexdef "-1-1-onto->" as
    "\raisebox{.5ex}{${\textstyle{\:}_{\mbox{\footnotesize\rm 1" +
    "\tt -\rm 1}}}\atop{\textstyle{" +
    "\longrightarrow}\atop{\textstyle{}^{\mbox{\footnotesize\rm onto}}}}$}";
htmldef "`" as
    "<IMG SRC='backtick.gif' WIDTH=4 HEIGHT=19 ALT=' ` ' TITLE='` '>";
    /* Above, IE7 _printing_ is corrupted by '`'; use '` ' which works */
  /*althtmldef "`" as ' &lsquo;';*/
  /* I took out the leading space to make e.g. ( log ` A ) look better.
     I added the leading space a long time ago because the quote overlapped
     the character to its left, making it sometimes hidden, but that seems
     to be no longer a problem with the XITS font. - 29-Aug-2017 nm */
  althtmldef "`" as '&lsquo;';
  latexdef "`" as "`";
htmldef "Isom" as
    " <IMG SRC='_isom.gif' WIDTH=30 HEIGHT=19 ALT=' Isom' TITLE='Isom'> ";
  althtmldef "Isom" as ' Isom ';
  latexdef "Isom" as "{\rm Isom}";
htmldef "oF" as
    " <IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' o' TITLE='o'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT=' F' TITLE='F'>";
  althtmldef "oF" as " &#8728;<SUB>&#x1D453;</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "oF" as "\circ_f";
htmldef "oR" as
    " <IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' o' TITLE='o'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT=' R' TITLE='R'>";
  althtmldef "oR" as " &#8728;<SUB>&#x1D45F;</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "oR" as "\circ_r";
htmldef "1st" as
    "<IMG SRC='_1st.gif' WIDTH=15 HEIGHT=19 ALT=' 1st' TITLE='1st'>";
  althtmldef "1st" as '1<SUP>st</SUP> ';
  latexdef "1st" as "1^{\rm st}";
htmldef "2nd" as
    "<IMG SRC='_2nd.gif' WIDTH=21 HEIGHT=19 ALT=' 2nd' TITLE='2nd'>";
  althtmldef "2nd" as '2<SUP>nd</SUP> ';
  latexdef "2nd" as "2^{\rm nd}";
htmldef "tpos" as "tpos ";
  althtmldef "tpos" as 'tpos ';
  latexdef "tpos" as "{\rm tpos}";
htmldef "curry" as "curry ";
  althtmldef "curry" as 'curry ';
  latexdef "curry" as "{\rm curry}";
htmldef "uncurry" as "uncurry ";
  althtmldef "uncurry" as 'uncurry ';
  latexdef "uncurry" as "{\rm uncurry}";
htmldef "[C.]" as
    " [<IMG SRC='subset.gif' WIDTH=12 HEIGHT=19 ALT=' C.' TITLE='C.'>] ";
  althtmldef "[C.]" as " [<B>&sub;</B>] ";
  latexdef "[C.]" as "{\rm [C.]}";
/*
htmldef "iota" as
    "<IMG SRC='iota.gif' WIDTH=6 HEIGHT=19 ALT=' iota' TITLE='iota'>";
  althtmldef "iota" as '<FONT SIZE="+1">&iota;</FONT>';
  latexdef "iota" as "\iota";
*/
/* 30-Nov-2013 changed to rotated iota */
htmldef "iota" as
    "<IMG SRC='riota.gif' WIDTH=6 HEIGHT=19 ALT=' iota' TITLE='iota'>";
  althtmldef "iota" as '&#8489;';
  latexdef "iota" as "\mathrm{\rotatebox[origin=C]{180}{$\iota$}}";
htmldef "Smo" as
    "<IMG SRC='_smo.gif' WIDTH=27 HEIGHT=19 ALT=' Smo' TITLE='Smo'> ";
  althtmldef "Smo" as "Smo ";
  latexdef "Smo" as "{\rm Smo}";
htmldef "recs" as "recs";
  althtmldef "recs" as "recs";
  latexdef "recs" as "\mathrm{recs}";
htmldef "rec" as
    "<IMG SRC='_rec.gif' WIDTH=21 HEIGHT=19 ALT=' rec' TITLE='rec'>";
  althtmldef "rec" as 'rec';
  latexdef "rec" as "{\rm rec}";
htmldef "seqom" as "seq<SUB>&#x1D714;</SUB>";
  althtmldef "seqom" as "seq<SUB>&#x1D714;</SUB>";
  latexdef "seqom" as "{\rm seqom}";
htmldef "1o" as "<IMG SRC='_1o.gif' WIDTH=13 HEIGHT=19 ALT=' 1o' TITLE='1o'>";
  althtmldef "1o" as '1<SUB>&#x1D45C;</SUB>';
  latexdef "1o" as "1_o";
htmldef "2o" as "<IMG SRC='_2o.gif' WIDTH=14 HEIGHT=19 ALT=' 2o' TITLE='2o'>";
  althtmldef "2o" as '2<SUB>&#x1D45C;</SUB>';
  latexdef "2o" as "2_o";
htmldef "3o" as "<IMG SRC='_3o.gif' WIDTH=14 HEIGHT=19 ALT=' 3o' TITLE='3o'>";
  althtmldef "3o" as "3<SUB>&#x1D45C;</SUB>"; latexdef "3o" as "3_o";
htmldef "4o" as "<IMG SRC='_4o.gif' WIDTH=15 HEIGHT=19 ALT=' 4o' TITLE='4o'>";
  althtmldef "4o" as "4<SUB>&#x1D45C;</SUB>"; latexdef "4o" as "4_o";
htmldef "+o" as
    " <IMG SRC='_plo.gif' WIDTH=18 HEIGHT=19 ALT=' +o' TITLE='+o'> ";
  althtmldef "+o" as ' +<SUB>&#x1D45C;</SUB> ';
  latexdef "+o" as "+_o";
htmldef ".o" as
    " <IMG SRC='_cdo.gif' WIDTH=10 HEIGHT=19 ALT=' .o' TITLE='.o'> ";
  althtmldef ".o" as ' &middot;<SUB>&#x1D45C;</SUB> ';
  latexdef ".o" as "\cdot_o";
htmldef "^o" as
    " <IMG SRC='_hato.gif' WIDTH=11 HEIGHT=19 ALT=' ^o' TITLE='^o'> ";
  althtmldef "^o" as ' &uarr;<SUB>&#x1D45C;</SUB> ';
  latexdef "^o" as "\uparrow_o"; /*
  latexdef "^o" as "\hat{\ }_o"; */
htmldef "Er" as
    " <IMG SRC='_er.gif' WIDTH=16 HEIGHT=19 ALT=' Er' TITLE='Er'> ";
  althtmldef "Er" as ' Er ';
  latexdef "Er" as "{\rm Er}";
htmldef "/." as
    "<IMG SRC='diagup.gif' WIDTH=14 HEIGHT=19 ALT=' /.' TITLE='/.'>";
  althtmldef "/." as ' <B>/</B> ';
  latexdef "/." as "\diagup";
htmldef "^m" as
    " <IMG SRC='_hatm.gif' WIDTH=15 HEIGHT=19 ALT=' ^m' TITLE='^m'> ";
  althtmldef "^m" as ' &uarr;<SUB>&#x1D45A;</SUB> ';
  latexdef "^m" as "\uparrow_m";
htmldef "^pm" as
    " <IMG SRC='_hatpm.gif' WIDTH=21 HEIGHT=19 ALT=' ^pm' TITLE='^pm'> ";
  althtmldef "^pm" as ' &uarr;<SUB><I>pm</I></SUB> ';
  latexdef "^pm" as "\uparrow_{pm}";
htmldef "X_" as
    "<IMG SRC='_bigtimes.gif' WIDTH=11 HEIGHT=19 ALT=' X_' TITLE='X_'>";
  althtmldef "X_" as '<FONT SIZE="+1">X</FONT>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "X_" as "\mbox{\large\boldmath$\times$}";
htmldef "~~" as
    " <IMG SRC='approx.gif' WIDTH=13 HEIGHT=19 ALT=' ~~' TITLE='~~'> ";
  althtmldef "~~" as ' &#8776; '; /* &ap; */
  latexdef "~~" as "\approx";
htmldef "~<_" as
   " <IMG SRC='preccurlyeq.gif' WIDTH=11 HEIGHT=19 " +
    "ALT=' ~&lt;_' TITLE='~&lt;_'> ";
  althtmldef "~<_" as ' &#8828; '; /* &prcue; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~<_" as "\preccurlyeq";
htmldef "~<" as
    " <IMG SRC='prec.gif' WIDTH=11 HEIGHT=19 ALT=' ~&lt;' TITLE='~&lt;'> ";
  althtmldef "~<" as ' &#8826; '; /* &pr; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~<" as "\prec";
htmldef "Fin" as
    "<IMG SRC='_fin.gif' WIDTH=21 HEIGHT=19 ALT=' Fin' TITLE='Fin'>";
  althtmldef "Fin" as 'Fin';
  latexdef "Fin" as "{\rm Fin}";
htmldef "Undef" as
    "<IMG SRC='_undef.gif' WIDTH=39 HEIGHT=19 ALT=' Undef' TITLE='Undef'>";
  althtmldef "Undef" as "Undef";
  latexdef "Undef" as "{\rm Undef}";
htmldef "iota_" as
    "<IMG SRC='_riotabar.gif' WIDTH=6 HEIGHT=19 ALT=' iota_' TITLE='iota_'>";
  althtmldef "iota_" as '<U>&#8489;</U> ';
  latexdef "iota_" as
      "\underline{\mathrm{\rotatebox[origin=C]{180}{$\iota$}}}";
htmldef "fi" as
    "<IMG SRC='_fi.gif' WIDTH=10 HEIGHT=19 ALT=' fi' TITLE='fi'>";
  althtmldef "fi" as "fi";
  latexdef "fi" as "{\rm fi}";
htmldef "sup" as
    "<IMG SRC='_sup.gif' WIDTH=22 HEIGHT=19 ALT=' sup' TITLE='sup'>";
  althtmldef "sup" as 'sup';
  latexdef "sup" as "{\rm sup}";
htmldef "OrdIso" as "OrdIso";
  althtmldef "OrdIso" as 'OrdIso';
  latexdef "OrdIso" as "{\rm OrdIso}";
/* the standard symbol for this is \aleph, but that collides */
htmldef "har" as "har";
  althtmldef "har" as "har";
  latexdef "har" as "{\rm har}";
htmldef "~<_*" as " <IMG SRC='preccurlyeq.gif' WIDTH=11 HEIGHT=19 " +
   "ALT=' ~&lt;_' TITLE='~&lt;_'><SUP>*</SUP> ";
  althtmldef "~<_*" as ' &#8828;<SUP>*</SUP> ';
  /* &prcue; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~<_*" as "\preccurlyeq^*";
htmldef "CNF" as " CNF ";
  althtmldef "CNF" as " CNF ";
  latexdef "CNF" as " {\rm CNF} ";
htmldef "TC" as
    "<IMG SRC='_tc.gif' WIDTH=20 HEIGHT=19 ALT=' TC' TITLE='TC'>";
  althtmldef "TC" as "TC";
  latexdef "TC" as "{\rm TC}";
htmldef "R1" as "<IMG SRC='_r1.gif' WIDTH=15 HEIGHT=19 ALT=' R1' TITLE='R1'>";
  althtmldef "R1" as '&#x1D445;<SUB>1</SUB>';
  latexdef "R1" as "R_1";
htmldef "rank" as
    "<IMG SRC='_rank.gif' WIDTH=30 HEIGHT=19 ALT=' rank' TITLE='rank'>";
  althtmldef "rank" as 'rank';
  latexdef "rank" as "{\rm rank}";
htmldef "card" as
    "<IMG SRC='_card.gif' WIDTH=30 HEIGHT=19 ALT=' card' TITLE='card'>";
  althtmldef "card" as 'card';
  latexdef "card" as "{\rm card}";
htmldef "aleph" as
    "<IMG SRC='varaleph.gif' WIDTH=12 HEIGHT=19 ALT=' aleph' TITLE='aleph'>";
  althtmldef "aleph" as '&#8501;'; /* &aleph; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "aleph" as "\aleph";
htmldef "cf" as
    "<IMG SRC='_cofin.gif' WIDTH=14 HEIGHT=19 ALT=' cf' TITLE='cf'>";
  althtmldef "cf" as 'cf';
  latexdef "cf" as "{\rm cf}";
htmldef "AC_" as '<U>AC</U> ';
  althtmldef "AC_" as '<U>AC</U> ';
  latexdef "AC_" as "\underline{\rm AC}";
htmldef "CHOICE" as "<SMALL>CHOICE</SMALL>";
  althtmldef "CHOICE" as "<SMALL>CHOICE</SMALL>";
  latexdef "CHOICE" as "\mathrm{CHOICE}";
htmldef "+c" as
    " <IMG SRC='_plc.gif' WIDTH=17 HEIGHT=19 ALT=' +c' TITLE='+c'> ";
  althtmldef "+c" as ' +<SUB>&#x1D450;</SUB> ';
  latexdef "+c" as "+_c";
htmldef "Fin1a" as "Fin<SUP>Ia</SUP>";
  althtmldef "Fin1a" as "Fin<SUP>Ia</SUP>";
  latexdef "Fin1a" as "{\rm Fin1a}";
htmldef "Fin2" as "Fin<SUP>II</SUP>";
  althtmldef "Fin2" as "Fin<SUP>II</SUP>";
  latexdef "Fin2" as "{\rm Fin2}";
htmldef "Fin3" as "Fin<SUP>III</SUP>";
  althtmldef "Fin3" as "Fin<SUP>III</SUP>";
  latexdef "Fin3" as "{\rm Fin3}";
htmldef "Fin4" as "Fin<SUP>IV</SUP>";
  althtmldef "Fin4" as "Fin<SUP>IV</SUP>";
  latexdef "Fin4" as "{\rm Fin4}";
htmldef "Fin5" as "Fin<SUP>V</SUP>";
  althtmldef "Fin5" as "Fin<SUP>V</SUP>";
  latexdef "Fin5" as "{\rm Fin5}";
htmldef "Fin6" as "Fin<SUP>VI</SUP>";
  althtmldef "Fin6" as "Fin<SUP>VI</SUP>";
  latexdef "Fin6" as "{\rm Fin6}";
htmldef "Fin7" as "Fin<SUP>VII</SUP>";
  althtmldef "Fin7" as "Fin<SUP>VII</SUP>";
  latexdef "Fin7" as "{\rm Fin7}";
htmldef "GCH" as "GCH";
  althtmldef "GCH" as "GCH";
  latexdef "GCH" as "{\rm GCH}";
htmldef "WUni" as "WUni";
  althtmldef "WUni" as "WUni";
  latexdef "WUni" as "{\rm WUni}";
htmldef "wUniCl" as "wUniCl";
  althtmldef "wUniCl" as "wUniCl";
  latexdef "wUniCl" as "{\rm wUniCl}";
htmldef "InaccW" as
    "<IMG SRC='_inacc.gif' WIDTH=34 HEIGHT=19 ALT=' Inacc' TITLE='Inacc'>" +
    "<IMG SRC='subw.gif' WIDTH=7 HEIGHT=19 ALT=' W' TITLE='W'>";
  althtmldef "InaccW" as " Inacc<SUB>&#x1D464;</SUB> ";
  latexdef "InaccW" as "{\rm Inacc}_w";
htmldef "Inacc" as
    "<IMG SRC='_inacc.gif' WIDTH=34 HEIGHT=19 ALT=' Inacc' TITLE='Inacc'>";
  althtmldef "Inacc" as "Inacc";
  latexdef "Inacc" as "{\rm Inacc}";
htmldef "Tarski" as
    "<IMG SRC='_tarski.gif' WIDTH=40 HEIGHT=19 ALT=' Tarski' TITLE='Tarski'>";
  althtmldef "Tarski" as "Tarski";
  latexdef "Tarski" as "{\rm Tarski}";
htmldef "Univ" as
    "<IMG SRC='_univ.gif' WIDTH=30 HEIGHT=19 ALT=' Univ' TITLE='Univ'>";
  althtmldef "Univ" as "Univ";
  latexdef "Univ" as "{\rm Univ}";
htmldef "tarskiMap" as "<IMG SRC='_tarskimap.gif' WIDTH=66 HEIGHT=19 " +
    "ALT=' tarskiMap' TITLE='tarskiMap'>";
  althtmldef "tarskiMap" as "tarskiMap";
  latexdef "tarskiMap" as "{\rm tarskiMap}";
htmldef "N." as "<IMG SRC='caln.gif' WIDTH=17 HEIGHT=19 ALT=' N.' TITLE='N.'>";
  althtmldef "N." as '<I><B>N</B></I>';
  latexdef "N." as "{\cal N}";
htmldef "+N" as
    " <IMG SRC='_pln.gif' WIDTH=22 HEIGHT=19 ALT=' +N' TITLE='+N'> ";
  althtmldef "+N" as ' +<I><SUB><B>N</B></SUB></I> ';
  latexdef "+N" as "+_{\cal N}";
htmldef ".N" as
    " <IMG SRC='_cdn.gif' WIDTH=14 HEIGHT=19 ALT=' .N' TITLE='.N'> ";
  althtmldef ".N" as ' &middot;<I><SUB><B>N</B></SUB></I> ';
  latexdef ".N" as "\cdot_{\cal N}";
htmldef "<N" as
    " <IMG SRC='_ltn.gif' WIDTH=21 HEIGHT=19 ALT=' &lt;N' TITLE='&lt;N'> ";
  althtmldef "<N" as ' &lt;<I><SUB><B>N</B></SUB></I> ';
  latexdef "<N" as "<_{\cal N}";
htmldef "+pQ" as
    " <IMG SRC='_plpq.gif' WIDTH=28 HEIGHT=19 ALT=' +pQ' TITLE='+pQ'> ";
  althtmldef "+pQ" as ' +<I><SUB>p<B>Q</B></SUB></I> ';
  latexdef "+pQ" as "+_{p{\cal Q}}";
htmldef ".pQ" as
    " <IMG SRC='_cdpq.gif' WIDTH=19 HEIGHT=19 ALT=' .pQ' TITLE='.pQ'> ";
  althtmldef ".pQ" as ' &middot;<I><SUB>p<B>Q</B></SUB></I> ';
  latexdef ".pQ" as "\cdot_{p{\cal Q}}";
htmldef "<pQ" as
    " <IMG SRC='_ltpq.gif' WIDTH=27 HEIGHT=19 ALT=' &lt;pQ' TITLE='&lt;pQ'> ";
  althtmldef "<pQ" as ' &lt;<I><SUB>p<B>Q</B></SUB></I> ';
  latexdef "<pQ" as "<_{p{\cal Q}}";
htmldef "~Q" as
    " <IMG SRC='_simq.gif' WIDTH=21 HEIGHT=19 ALT=' ~Q' TITLE='~Q'> ";
  althtmldef "~Q" as ' ~<I><SUB><B>Q</B></SUB></I> ';
  latexdef "~Q" as "\sim_{\cal Q}";
htmldef "Q." as "<IMG SRC='calq.gif' WIDTH=12 HEIGHT=19 ALT=' Q.' TITLE='Q.'>";
  althtmldef "Q." as '<I><B>Q</B></I>';
  latexdef "Q." as "{\cal Q}";
htmldef "1Q" as "<IMG SRC='_1q.gif' WIDTH=16 HEIGHT=19 ALT=' 1Q' TITLE='1Q'>";
  althtmldef "1Q" as '1<I><SUB><B>Q</B></SUB></I>';
  latexdef "1Q" as "1_{\cal Q}";
htmldef "/Q" as "<IMG SRC='_erq.gif' WIDTH=17 HEIGHT=19 ALT=' /Q' TITLE='/Q'>";
  althtmldef "/Q" as '[<I><B>Q</B></I>]';
  latexdef "/Q" as "[{\cal Q}]";
htmldef "+Q" as
    " <IMG SRC='_plq.gif' WIDTH=21 HEIGHT=19 ALT=' +Q' TITLE='+Q'> ";
  althtmldef "+Q" as ' +<I><SUB><B>Q</B></SUB></I> ';
  latexdef "+Q" as "+_{\cal Q}";
htmldef ".Q" as
    " <IMG SRC='_cdq.gif' WIDTH=13 HEIGHT=19 ALT=' .Q' TITLE='.Q'> ";
  althtmldef ".Q" as ' &middot;<I><SUB><B>Q</B></SUB></I> ';
  latexdef ".Q" as "\cdot_{\cal Q}";
htmldef "*Q" as
    "<IMG SRC='_astq.gif' WIDTH=16 HEIGHT=19 ALT=' *Q' TITLE='*Q'>";
  althtmldef "*Q" as '*<I><SUB><B>Q</B></SUB></I>';
  latexdef "*Q" as "\ast_{\cal Q}";
htmldef "<Q" as
    " <IMG SRC='_ltq.gif' WIDTH=20 HEIGHT=19 ALT=' &lt;Q' TITLE='&lt;Q'> ";
  althtmldef "<Q" as ' &lt;<I><SUB><B>Q</B></SUB></I> ';
  latexdef "<Q" as "<_{\cal Q}";
htmldef "P." as "<IMG SRC='calp.gif' WIDTH=13 HEIGHT=19 ALT=' P.' TITLE='P.'>";
  althtmldef "P." as '<I><B>P</B></I>';
  latexdef "P." as "{\cal P}";
htmldef "1P" as "<IMG SRC='_1p.gif' WIDTH=15 HEIGHT=19 ALT=' 1P' TITLE='1P'>";
  althtmldef "1P" as '1<I><SUB><B>P</B></SUB></I>';
  latexdef "1P" as "1_{\cal P}";
htmldef "+P." as
    " <IMG SRC='_plp.gif' WIDTH=22 HEIGHT=19 ALT=' +P.' TITLE='+P.'> ";
  althtmldef "+P." as ' +<I><SUB><B>P</B></SUB></I> ';
  latexdef "+P." as "+_{\cal P}";
htmldef ".P." as
    " <IMG SRC='_cdp.gif' WIDTH=13 HEIGHT=19 ALT=' .P.' TITLE='.P.'> ";
  althtmldef ".P." as ' &middot;<I><SUB><B>P</B></SUB></I> ';
  latexdef ".P." as "\cdot_{\cal P}";
htmldef "<P" as
    " <IMG SRC='_ltp.gif' WIDTH=19 HEIGHT=19 ALT=' &lt;P' TITLE='&lt;P'> ";
  althtmldef "<P" as '&lt;<I><SUB><B>P</B></SUB></I> ';
  latexdef "<P" as "<_{\cal P}";
htmldef "+pR" as
    " <IMG SRC='_plpr.gif' WIDTH=28 HEIGHT=19 ALT=' +pR' TITLE='+pR'> ";
  althtmldef "+pR" as ' +<I><SUB>p<B>R</B></SUB></I> ';
  latexdef "+pR" as "+_{p{\cal R}}";
htmldef ".pR" as
    " <IMG SRC='_cdpr.gif' WIDTH=19 HEIGHT=19 ALT=' .pR' TITLE='.pR'> ";
  althtmldef ".pR" as ' &middot;<I><SUB>p<B>R</B></SUB></I> ';
  latexdef ".pR" as "._{p{\cal R}}";
htmldef "~R" as
    " <IMG SRC='_simr.gif' WIDTH=23 HEIGHT=19 ALT=' ~R' TITLE='~R'> ";
  althtmldef "~R" as ' ~<I><SUB><B>R</B></SUB></I> ';
  latexdef "~R" as "\sim_{\cal R}";
htmldef "R." as "<IMG SRC='calr.gif' WIDTH=15 HEIGHT=19 ALT=' R.' TITLE='R.'>";
  althtmldef "R." as '<I><B>R</B></I>';
  latexdef "R." as "{\cal R}";
htmldef "0R" as "<IMG SRC='_0r.gif' WIDTH=18 HEIGHT=19 ALT=' 0R' TITLE='0R'>";
  althtmldef "0R" as '0<I><SUB><B>R</B></SUB></I>';
  latexdef "0R" as "0_{\cal R}";
htmldef "1R" as "<IMG SRC='_1cr.gif' WIDTH=16 HEIGHT=19 ALT=' 1R' TITLE='1R'>";
  althtmldef "1R" as '1<I><SUB><B>R</B></SUB></I>';
  latexdef "1R" as "1_{\cal R}";
htmldef "-1R" as
    "<IMG SRC='_m1r.gif' WIDTH=22 HEIGHT=19 ALT=' -1R' TITLE='-1R'>";
  althtmldef "-1R" as '-1<I><SUB><B>R</B></SUB></I>';
  latexdef "-1R" as "-1_{\cal R}";
htmldef "+R" as
    " <IMG SRC='_plr.gif' WIDTH=23 HEIGHT=19 ALT=' +R' TITLE='+R'> ";
  althtmldef "+R" as ' +<I><SUB><B>R</B></SUB></I> ';
  latexdef "+R" as "+_{\cal R}";
htmldef ".R" as
    " <IMG SRC='_cdcr.gif' WIDTH=14 HEIGHT=19 ALT=' .R' TITLE='.R'> ";
  althtmldef ".R" as ' &middot;<I><SUB><B>R</B></SUB></I> ';
  latexdef ".R" as "\cdot_{\cal R}";
htmldef "<R" as
    " <IMG SRC='_ltr.gif' WIDTH=20 HEIGHT=19 ALT=' &lt;R' TITLE='&lt;R'> ";
  althtmldef "<R" as ' &lt;<I><SUB><B>R</B></SUB></I> ';
  latexdef "<R" as "<_{\cal R}";
htmldef "<RR" as
    " <IMG SRC='_ltbbr.gif' WIDTH=20 HEIGHT=19 ALT=' &lt;RR' TITLE='&lt;RR'> ";
  althtmldef "<RR" as ' &lt;<SUB>&#8477;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "<RR" as "<_\mathbb{R}";
htmldef "CC" as "<IMG SRC='bbc.gif' WIDTH=12 HEIGHT=19 ALT=' CC' TITLE='CC'>";
  althtmldef "CC" as '&#8450;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "CC" as "\mathbb{C}";
htmldef "RR" as "<IMG SRC='bbr.gif' WIDTH=13 HEIGHT=19 ALT=' RR' TITLE='RR'>";
  althtmldef "RR" as '&#8477;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "RR" as "\mathbb{R}";
    /*latexdef "" as "_{10}";*/
    /*latexdef "" as "";*/
    /* suppress base 10 suffix */
htmldef "0" as "<IMG SRC='0.gif' WIDTH=8 HEIGHT=19 ALT=' 0' TITLE='0'>";
  althtmldef "0" as '0';
  latexdef "0" as "0";
htmldef "1" as "<IMG SRC='1.gif' WIDTH=7 HEIGHT=19 ALT=' 1' TITLE='1'>";
  althtmldef "1" as '1';
  latexdef "1" as "1";
htmldef "_i" as "<IMG SRC='rmi.gif' WIDTH=4 HEIGHT=19 ALT=' _i' TITLE='_i'>";
  althtmldef "_i" as 'i';
  latexdef "_i" as "{\rm i}";
htmldef "+" as " <IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'> ";
  althtmldef "+" as ' + ';
  latexdef "+" as "+";
htmldef "x." as
    " <IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' x.' TITLE='x.'> ";
  althtmldef "x." as ' &middot; '; /* what is &#xb7; ? */
  latexdef "x." as "\cdot";
htmldef "<_" as
    " <IMG SRC='le.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;_' TITLE='&lt;_'> ";
  althtmldef "<_" as ' &le; ';
  latexdef "<_" as "\le";
htmldef "+oo" as " <IMG SRC='_pinf.gif' WIDTH=29 HEIGHT=19 ALT=' +oo' " +
    "TITLE='+oo'>";
  althtmldef "+oo" as ' +&infin;';
  latexdef "+oo" as "+\infty";
htmldef "-oo" as " <IMG SRC='_minf.gif' WIDTH=24 HEIGHT=19 ALT=' -oo' " +
    "TITLE='-oo'>";
  althtmldef "-oo" as ' -&infin;';
  latexdef "-oo" as "-\infty";
htmldef "RR*" as "<IMG SRC='_bbrast.gif' WIDTH=18 HEIGHT=19 ALT=' RR*' " +
    "TITLE='RR*'>";
  althtmldef "RR*" as '&#8477;<SUP>*</SUP>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "RR*" as "\mathbb{R}^*";
htmldef "<" as
    " <IMG SRC='lt.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;' TITLE='&lt;'> ";
  althtmldef "<" as ' &lt; ';
  latexdef "<" as "<";
htmldef "-" as
    " <IMG SRC='minus.gif' WIDTH=11 HEIGHT=19 ALT=' -' TITLE='-'> ";
  althtmldef "-" as ' &minus; ';
  latexdef "-" as "-";
htmldef "-u" as
    "<IMG SRC='shortminus.gif' WIDTH=8 HEIGHT=19 ALT=' -u' TITLE='-u'>";
    /* use standard minus sign */
  althtmldef "-u" as '-';
  latexdef "-u" as "\textrm{-}"; /* short minus */
    /*latexdef "-u" as "-_u";*/
htmldef "NN" as "<IMG SRC='bbn.gif' WIDTH=12 HEIGHT=19 ALT=' NN' TITLE='NN'>";
  althtmldef "NN" as '&#8469;'; /* &Nopf; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "NN" as "\mathbb{N}";
htmldef "NN0" as
    "<IMG SRC='_bbn0.gif' WIDTH=19 HEIGHT=19 ALT=' NN0' TITLE='NN0'>";
  althtmldef "NN0" as '&#8469;<SUB>0</SUB>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "NN0" as "\mathbb{N}_0";
htmldef "ZZ" as "<IMG SRC='bbz.gif' WIDTH=11 HEIGHT=19 ALT=' ZZ' TITLE='ZZ'>";
  althtmldef "ZZ" as '&#8484;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "ZZ" as "\mathbb{Z}";
htmldef "QQ" as "<IMG SRC='bbq.gif' WIDTH=13 HEIGHT=19 ALT=' QQ' TITLE='QQ'>";
  althtmldef "QQ" as '&#8474;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "QQ" as "\mathbb{Q}";
htmldef "RR+" as "<IMG SRC='_bbrplus.gif' WIDTH=20 HEIGHT=19 ALT=' RR+' " +
    "TITLE='RR+'>";
  althtmldef "RR+" as '&#8477;<SUP>+</SUP>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "RR+" as "\mathbb{R}^+";
htmldef "2" as "<IMG SRC='2.gif' WIDTH=8 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "2" as '2';
  latexdef "2" as "2";
htmldef "3" as "<IMG SRC='3.gif' WIDTH=8 HEIGHT=19 ALT=' 3' TITLE='3'>";
  althtmldef "3" as '3';
  latexdef "3" as "3";
htmldef "4" as "<IMG SRC='4.gif' WIDTH=9 HEIGHT=19 ALT=' 4' TITLE='4'>";
  althtmldef "4" as '4';
  latexdef "4" as "4";
htmldef "5" as "<IMG SRC='5.gif' WIDTH=8 HEIGHT=19 ALT=' 5' TITLE='5'>";
  althtmldef "5" as '5';
  latexdef "5" as "5";
htmldef "6" as "<IMG SRC='6.gif' WIDTH=8 HEIGHT=19 ALT=' 6' TITLE='6'>";
  althtmldef "6" as '6';
  latexdef "6" as "6";
htmldef "7" as "<IMG SRC='7.gif' WIDTH=9 HEIGHT=19 ALT=' 7' TITLE='7'>";
  althtmldef "7" as '7';
  latexdef "7" as "7";
htmldef "8" as "<IMG SRC='8.gif' WIDTH=8 HEIGHT=19 ALT=' 8' TITLE='8'>";
  althtmldef "8" as '8';
  latexdef "8" as "8";
htmldef "9" as "<IMG SRC='9.gif' WIDTH=8 HEIGHT=19 ALT=' 9' TITLE='9'>";
  althtmldef "9" as '9';
  latexdef "9" as "9";
htmldef "10" as "<IMG SRC='_10.gif' WIDTH=14 HEIGHT=19 ALT=' 10' TITLE='10'>";
  althtmldef "10" as '10';
  latexdef "10" as "10";
htmldef ";" as '<FONT COLOR="#808080">;</FONT>';
  althtmldef ";" as '<SPAN CLASS=hidden STYLE="color:gray">;</SPAN>';
  latexdef ";" as "{\rm;}";
htmldef "ZZ>=" as "<IMG SRC='_bbzge.gif' WIDTH=20 HEIGHT=19 " +
    "ALT=' ZZ&gt;=' TITLE='ZZ&gt;='>";
  althtmldef "ZZ>=" as "&#8484;<SUB>&ge;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "ZZ>=" as "\mathbb{Z}_\ge";
htmldef "-e" as " <IMG SRC='shortminus.gif' WIDTH=8 HEIGHT=19 ALT=' -' " +
    "TITLE='-'><IMG SRC='sube.gif' WIDTH=6 HEIGHT=19 ALT=' e' TITLE='e'>";
  althtmldef "-e" as '-';
  latexdef "-e" as "\textrm{-}";
htmldef "+e" as "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='sube.gif' WIDTH=6 HEIGHT=19 ALT=' e' TITLE='e'>";
  althtmldef "+e" as " +<SUB>&#x1D452;</SUB> ";
  latexdef "+e" as "+_e";
htmldef "*e" as "<IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' x' TITLE='x'>" +
    "<IMG SRC='sube.gif' WIDTH=6 HEIGHT=19 ALT=' e' TITLE='e'>";
  althtmldef "*e" as  " &middot;<SUB>e</SUB> ";
  latexdef "*e" as "\cdot_e";
htmldef "(,)" as
    "<IMG SRC='_ioo.gif' WIDTH=13 HEIGHT=19 ALT=' (,)' TITLE='(,)'>";
  althtmldef "(,)" as "(,)";
  latexdef "(,)" as "(,)";
htmldef "(,]" as
    "<IMG SRC='_ioc.gif' WIDTH=12 HEIGHT=19 ALT=' (,]' TITLE='(,]'>";
  althtmldef "(,]" as "(,]";
  latexdef "(,]" as "(,]";
htmldef "[,)" as
    "<IMG SRC='_ico.gif' WIDTH=13 HEIGHT=19 ALT=' [,)' TITLE='[,)'>";
  althtmldef "[,)" as "[,)";
  latexdef "[,)" as "[,)";
htmldef "[,]" as
    "<IMG SRC='_icc.gif' WIDTH=12 HEIGHT=19 ALT=' [,]' TITLE='[,]'>";
  althtmldef "[,]" as "[,]";
  latexdef "[,]" as "[,]";
htmldef "..." as "<IMG SRC='ldots.gif' WIDTH=18 HEIGHT=19 " +
    "ALT=' ...' TITLE='...'>";
  althtmldef "..." as "...";
  latexdef "..." as "\ldots";
htmldef "..^" as "..^";
  althtmldef "..^" as "..^";
  latexdef "..^" as "..\^";
htmldef "|_" as "<IMG SRC='lfloor.gif' WIDTH=6 HEIGHT=19 ALT=' |_' " +
    "TITLE='|_'>";
  althtmldef "|_" as '&#8970;';
  latexdef "|_" as "\lfloor";
htmldef "mod" as " <IMG SRC='_mod.gif' WIDTH=29 HEIGHT=19 ALT=' mod' " +
    "TITLE='mod'> ";
  althtmldef "mod" as ' mod ';
  latexdef "mod" as "{\rm mod}";
htmldef "==" as " <IMG SRC='equiv.gif' WIDTH=12 HEIGHT=19 ALT=' ==' " +
    "TITLE='=='> ";
  althtmldef "==" as "&equiv;"; /* 2263 */
  latexdef "==" as "\equiv";
htmldef "seq" as " <IMG SRC='_seq.gif' WIDTH=22 HEIGHT=19 ALT=' seq' " +
    "TITLE='seq'> ";
  althtmldef "seq" as 'seq';
  latexdef "seq" as "{\rm seq}";
/*
htmldef "seq1" as " <IMG SRC='_seq1.gif' WIDTH=26 HEIGHT=19 ALT=' seq1' " +
    "TITLE='seq1'> ";
  althtmldef "seq1" as 'seq<SUB>1</SUB>';
  latexdef "seq1" as "{\rm seq}_1";
htmldef "seqz" as
    " <IMG SRC='_seq.gif' WIDTH=22 HEIGHT=19 ALT=' seq' TITLE='seq'>" +
    "<IMG SRC='__subbbz.gif' WIDTH=8 HEIGHT=19 ALT=' z' TITLE='z'> ";
  althtmldef "seqz" as 'seq<SUB><FONT FACE=sans-serif>&#8484;</FONT></SUB>';
  latexdef "seqz" as "{\rm seq}_\mathbb{Z}";
htmldef "seq0" as " <IMG SRC='_seq0.gif' WIDTH=27 HEIGHT=19 ALT=' seq0' " +
    "TITLE='seq0'> ";
  althtmldef "seq0" as 'seq<SUB>0</SUB>';
  latexdef "seq0" as "{\rm seq}_0";
*/
htmldef "^" as "<IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' TITLE='^'>";
  althtmldef "^" as '&uarr;';
  latexdef "^" as "\uparrow"; /*
  latexdef "^" as "\widehat{\ }"; */
htmldef "!" as "<IMG SRC='bang.gif' WIDTH=3 HEIGHT=19 ALT=' !' TITLE='!'>";
  althtmldef "!" as '!';
  latexdef "!" as "{!}";
htmldef "_C" as
    " <IMG SRC='rmcc.gif' WIDTH=10 HEIGHT=19 ALT=' _C' TITLE='_C'> ";
  althtmldef "_C" as 'C';
  latexdef "_C" as "{\rm C}";
htmldef "#" as
    "<IMG SRC='octothorpe.gif' WIDTH=13 HEIGHT=19 ALT=' #' TITLE='#'>";
  althtmldef "#" as "#";
  latexdef "#" as "#";
htmldef "shift" as " <IMG SRC='_shift.gif' WIDTH=30 HEIGHT=19 ALT=' shift' " +
    "TITLE='shift'> ";
  althtmldef "shift" as 'shift';
  latexdef "shift" as "{\rm shift}";
htmldef "Re" as "<IMG SRC='re.gif' WIDTH=12 HEIGHT=19 ALT=' Re' TITLE='Re'>";
  althtmldef "Re" as '&real;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Re" as "\Re";
htmldef "Im" as "<IMG SRC='im.gif' WIDTH=12 HEIGHT=19 ALT=' Im' TITLE='Im'>";
  althtmldef "Im" as '&image;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Im" as "\Im";
htmldef "*" as "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT=' *' TITLE='*'>";
  althtmldef "*" as '&lowast;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "*" as "*";
htmldef "sqr" as
    "<IMG SRC='surd.gif' WIDTH=14 HEIGHT=19 ALT=' sqr' TITLE='sqr'>";
  althtmldef "sqr" as '&radic;';
  latexdef "sqr" as "\surd";
htmldef "abs" as
    "<IMG SRC='_abs.gif' WIDTH=22 HEIGHT=19 ALT=' abs' TITLE='abs'>";
  althtmldef "abs" as 'abs';
  latexdef "abs" as "{\rm abs}";
htmldef "+-" as
    "<IMG SRC='pm.gif' WIDTH=14 HEIGHT=19 ALT=' pm' TITLE='pm'>";
  althtmldef "+-" as '&plusmn;';
  latexdef "+-" as "\pm";
htmldef "limsup" as
    "<IMG SRC='_limsup.gif' WIDTH=44 HEIGHT=19 ALT=' limsup' TITLE='limsup'>";
  althtmldef "limsup" as 'lim sup';
  latexdef "limsup" as "\limsup";
htmldef "~~>" as " <IMG SRC='rightsquigarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' ~~&gt;' TITLE='~~&gt;'> ";
  althtmldef "~~>" as ' &#8669; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~~>" as '\rightsquigarrow';
htmldef "~~>r" as " <IMG SRC='rightsquigarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' ~~&gt;' TITLE='~~&gt;'><IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 " +
    "ALT=' r' TITLE='r'> ";
  althtmldef "~~>r" as
    ' &#8669;<SUB>&#x1D45F;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~~>r" as '\rightsquigarrow_r';
htmldef "O(1)" as "<IMG SRC='co.gif' WIDTH=12 HEIGHT=19 ALT=' O' TITLE='O'>" +
    "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT=' (' TITLE='('>" +
    "<IMG SRC='1.gif' WIDTH=7 HEIGHT=19 ALT=' 1' TITLE='1'>" +
    "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=' )' TITLE=')'>";
  althtmldef "O(1)" as '&#x1D442;(1)';
  latexdef "O(1)" as "O(1)";
htmldef "<_O(1)" as
    "<IMG SRC='le.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;_' TITLE='&lt;_'>" +
    "<IMG SRC='co.gif' WIDTH=12 HEIGHT=19 ALT=' O' TITLE='O'>" +
    "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT=' (' TITLE='('>" +
    "<IMG SRC='1.gif' WIDTH=7 HEIGHT=19 ALT=' 1' TITLE='1'>" +
    "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=' )' TITLE=')'>";
  althtmldef "<_O(1)" as '&le;&#x1D442;(1)';
  latexdef "<_O(1)" as "\le O(1)";
htmldef "sum_" as "<IMG SRC='csigma.gif' WIDTH=11 HEIGHT=19 " +
    "ALT=' sum_' TITLE='sum_'>";
  althtmldef "sum_" as "&Sigma;";
  latexdef "sum_" as "\Sigma";
htmldef "exp" as
    "<IMG SRC='_exp.gif' WIDTH=24 HEIGHT=19 ALT=' exp' TITLE='exp'>";
  althtmldef "exp" as "exp";
  latexdef "exp" as "\exp";
htmldef "_e" as "<IMG SRC='rme.gif' WIDTH=7 HEIGHT=19 ALT=' _e' TITLE='_e'>";
  althtmldef "_e" as "e";
  latexdef "_e" as "{\rm e}";
htmldef "sin" as
    "<IMG SRC='_sin.gif' WIDTH=19 HEIGHT=19 ALT=' sin' TITLE='sin'>";
  althtmldef "sin" as "sin";
  latexdef "sin" as "\sin";
htmldef "cos" as
    "<IMG SRC='_cos.gif' WIDTH=21 HEIGHT=19 ALT=' cos' TITLE='cos'>";
  althtmldef "cos" as "cos";
  latexdef "cos" as "\cos";
htmldef "tan" as
    "<IMG SRC='_tan.gif' WIDTH=22 HEIGHT=19 ALT=' tan' TITLE='tan'>";
  althtmldef "tan" as "tan";
  latexdef "tan" as "\tan";
htmldef "pi" as "<IMG SRC='pi.gif' WIDTH=10 HEIGHT=19 ALT=' pi' TITLE='pi'>";
  althtmldef "pi" as "&#x1D70B;"; /* math italic pi */
  latexdef "pi" as "\pi";
htmldef "||" as " <IMG SRC='parallel.gif' WIDTH=5 HEIGHT=19 " +
    "ALT=' ||' TITLE='||'> ";
  althtmldef "||" as ' &#8741; ';
  latexdef "||" as " \parallel ";
htmldef "bits" as "bits";
  althtmldef "bits" as "bits";
  latexdef "bits" as "\mbox{bits}";
htmldef "sadd" as " sadd ";
  althtmldef "sadd" as " sadd ";
  latexdef "sadd" as "\mbox{sadd}";
htmldef "smul" as " smul ";
  althtmldef "smul" as " smul ";
  latexdef "smul" as "\mbox{smul}";
htmldef "gcd" as
    " <IMG SRC='_gcd.gif' WIDTH=23 HEIGHT=19 ALT=' gcd' TITLE='gcd'> ";
  althtmldef "gcd" as " gcd ";
  latexdef "gcd" as "\,{\rm gcd}\,";
htmldef "Prime" as
    "<IMG SRC='bbp.gif' WIDTH=11 HEIGHT=19 ALT=' Prime' TITLE='Prime'>";
  althtmldef "Prime" as "&#8473;";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Prime" as "\mathbb{P}";
htmldef "odZ" as
    "<IMG SRC='_od.gif' WIDTH=15 HEIGHT=19 ALT=' od' TITLE='od'>" +
    "<IMG SRC='__subbbz.gif' WIDTH=8 HEIGHT=19 ALT=' Z' TITLE='Z'>";
  althtmldef "odZ" as "od<SUB>&#8484;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "odZ" as "{\rm od}_{\Bbb Z}";
htmldef "phi" as
    "<IMG SRC='phi.gif' WIDTH=10 HEIGHT=19 ALT=' phi' TITLE='phi'>";
  althtmldef "phi" as '&#981;';
  latexdef "phi" as "\phi";
htmldef "pCnt" as
    " <IMG SRC='_pcnt.gif' WIDTH=32 HEIGHT=19 ALT=' pCnt' TITLE='pCnt'> ";
  althtmldef "pCnt" as " pCnt ";
  latexdef "pCnt" as "\,{\rm pCnt}\,";
htmldef "Z[i]" as
    "<IMG SRC='bbz.gif' WIDTH=11 HEIGHT=19 ALT=' ZZ' TITLE='ZZ'>" +
    "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 ALT=' [' TITLE='['>" +
    "<IMG SRC='rmi.gif' WIDTH=4 HEIGHT=19 ALT=' _i' TITLE='_i'>" +
    "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 ALT=' ]' TITLE=']'>";
  althtmldef "Z[i]" as '&#8484;[i]';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Z[i]" as "\mathbb{Z}[{\rm i}]";
htmldef "AP" as "AP";
  althtmldef "AP" as "AP";
  latexdef "AP" as "{\rm AP}";
htmldef "MonoAP" as " MonoAP ";
  althtmldef "MonoAP" as " MonoAP ";
  latexdef "MonoAP" as " {\rm MonoAP} ";
htmldef "PolyAP" as " PolyAP ";
  althtmldef "PolyAP" as " PolyAP ";
  latexdef "PolyAP" as " {\rm PolyAP} ";
htmldef "Ramsey" as " Ramsey ";
  althtmldef "Ramsey" as " Ramsey ";
  latexdef "Ramsey" as " {\rm Ramsey} ";
htmldef "Struct" as " Struct ";
  althtmldef "Struct" as " Struct ";
  latexdef "Struct" as " {\rm Struct} ";
htmldef "ndx" as
    "<IMG SRC='_ndx.gif' WIDTH=24 HEIGHT=19 ALT=' ndx' TITLE='ndx'>";
  althtmldef "ndx" as "ndx";
  latexdef "ndx" as "{\rm ndx}";
htmldef "sSet" as " sSet "; althtmldef "sSet" as " sSet ";
  latexdef "sSet" as "{\rm sSet}";
htmldef "Slot" as "Slot ";
  althtmldef "Slot" as "Slot ";
  latexdef "Slot" as "{\rm Slot} ";
htmldef "Base" as
    "<IMG SRC='_base.gif' WIDTH=30 HEIGHT=19 ALT=' Base' TITLE='Base'>";
  althtmldef "Base" as "Base";
  latexdef "Base" as "{\rm Base}";
htmldef "|`s" as " &#8638;<SUB>s</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "|`s" as " &#8638;<SUB>s</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|`s" as "\restriction_s";
htmldef "+g" as
    "<IMG SRC='_plusg.gif' WIDTH=19 HEIGHT=19 ALT=' +g' TITLE='+g'> ";
  althtmldef "+g" as "+<SUB>g</SUB>";
  latexdef "+g" as "+_{\rm g}";
htmldef ".r" as "<IMG SRC='_cdr.gif' WIDTH=10 HEIGHT=19 ALT=' .r' TITLE='.r'>";
  althtmldef ".r" as ".<SUB>r</SUB>";
  latexdef ".r" as "._{\rm r}";
htmldef "*r" as "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT=' *' TITLE='*'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT=' r' TITLE='r'>";
  althtmldef "*r" as "*<SUB>&#x1D45F;</SUB>";
  latexdef "*r" as "\ast_r";
htmldef "Scalar" as "Scalar";
  althtmldef "Scalar" as "Scalar";
  latexdef "Scalar" as "{\rm Scalar}";
htmldef ".s" as "<IMG SRC='_cds.gif' WIDTH=9 HEIGHT=19 ALT=' .s' TITLE='.s'>";
  althtmldef ".s" as ' <B>&middot;</B><SUB>&#x1D460;</SUB> ';
  latexdef ".s" as '\cdot_s';
htmldef ".i" as "<IMG SRC='_cdi.gif' WIDTH=7 HEIGHT=19 ALT=' .i' TITLE='.i'>";
  althtmldef ".i" as '<B>&middot;</B><SUB>&#x1D456;</SUB>';
  latexdef ".i" as '\cdot_i';
htmldef "TopSet" as "TopSet";
  althtmldef "TopSet" as "TopSet";
  latexdef "TopSet" as "{\rm TopSet}";
htmldef "le" as
    "<IMG SRC='_rmle.gif' WIDTH=11 HEIGHT=19 ALT=' le' TITLE='le'>";
  althtmldef "le" as "le";
  latexdef "le" as "{\rm le}";
htmldef "oc" as "<IMG SRC='_oc.gif' WIDTH=14 HEIGHT=19 ALT=' oc' TITLE='oc'>";
  althtmldef "oc" as "oc";
  latexdef "oc" as "{\rm oc}";
htmldef "dist" as
    "<IMG SRC='_dist.gif' WIDTH=24 HEIGHT=19 ALT=' dist' TITLE='dist'>";
  althtmldef "dist" as "dist";
  latexdef "dist" as "{\rm dist}";
htmldef "UnifSet" as
    "<IMG SRC='_unif.gif' WIDTH=28 HEIGHT=19 ALT=' UnifSet' TITLE='UnifSet'>";
  althtmldef "UnifSet" as "UnifSet";
  latexdef "UnifSet" as "{\rm UnifSet}";
htmldef "Hom" as
    " <IMG SRC='_hom.gif' WIDTH=27 HEIGHT=19 ALT=' Hom' TITLE='Hom'> ";
  althtmldef "Hom" as " Hom ";
  latexdef "Hom" as "{\rm Hom}";
htmldef "comp" as "comp";
  althtmldef "comp" as "comp";
  latexdef "comp" as "{\rm comp}";
htmldef "|`t" as " &#8638;<SUB>t</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "|`t" as " &#8638;<SUB>t</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|`t" as "\restriction_t";
htmldef "TopOpen" as
  "<IMG SRC='_topopen.gif' WIDTH=57 HEIGHT=19 ALT=' TopOpen' TITLE='TopOpen'>";
  althtmldef "TopOpen" as "TopOpen";
  latexdef "TopOpen" as "{\rm TopOpen}";
htmldef "topGen" as
    "<IMG SRC='_topgen.gif' WIDTH=47 HEIGHT=19 ALT=' topGen' TITLE='topGen'>";
  althtmldef "topGen" as "topGen";
  latexdef "topGen" as "{\rm topGen}";
htmldef "Xt_" as
    "<IMG SRC='_prodt.gif' WIDTH=17 HEIGHT=19 ALT=' Xt_' TITLE='Xt_'>";
  althtmldef "Xt_" as "&prod;<SUB>t</SUB>";
  latexdef "Xt_" as "\prod_t";
htmldef "Xs_" as "<IMG SRC='_bigtimes.gif' WIDTH=11 HEIGHT=19 ALT=' X_' " +
    "TITLE='X_'><sub><i>s</i></sub>";
  althtmldef "Xs_" as
    "<FONT SIZE='+1' FACE=sans-serif>X</FONT><sub><i>s</i></sub>";
  latexdef "Xs_" as "\mbox{\large\boldmath$\times$}_s";
htmldef "^s" as " <IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' " +
    "TITLE='^'><sub><i>s</i></sub> ";
  althtmldef "^s" as ' &uarr;<sub><i>s</i></sub> ';
  latexdef "^s" as " \uparrow_s ";
htmldef "ordTop" as "ordTop";
  althtmldef "ordTop" as "ordTop";
  latexdef "ordTop" as "{\rm ordTop}";
htmldef "RR*s" as
    "<IMG SRC='_bbrast.gif' WIDTH=18 HEIGHT=19 ALT=' RR*' TITLE='RR*'>" +
    "<IMG SRC='subs.gif' WIDTH=6 HEIGHT=19 ALT=' s' TITLE='s'>";
  althtmldef "RR*s" as
    '&#8477;<SUP>*</SUP><SUB>&#x1D460;</SUB>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "RR*s" as "\mathbb{R}^*_s";
htmldef "0g" as "<IMG SRC='_0g.gif' WIDTH=14 HEIGHT=19 ALT=' 0g' TITLE='0g'>";
  althtmldef "0g" as "0<SUB>g</SUB>";
  latexdef "0g" as "0_{\rm g}";
htmldef "gsum" as " <IMG SRC='csigma.gif' WIDTH=11 HEIGHT=19 " +
    "ALT=' gsum' TITLE='gsum'><sub><i>g</i></sub> ";
  althtmldef "gsum" as " &Sigma;<sub><i>g</i></sub> ";
  latexdef "gsum" as " \Sigma_g ";
htmldef '"s' as " <IMG SRC='backquote.gif' WIDTH=7 HEIGHT=19 ALT=' " + '"' +
    "' TITLE='" + '"' + "'><sub><i>s</i></sub> ";
  althtmldef '"s' as ' &ldquo;<sub><i>s</i></sub> ';
  latexdef '"s' as "``_s";
htmldef "/s" as " <IMG SRC='diagup.gif' WIDTH=14 HEIGHT=19 ALT=' /.' " +
    "TITLE='/.'><sub><i>s</i></sub> ";
  althtmldef "/s" as " /<sub><i>s</i></sub> ";
  latexdef "/s" as " \diagup_s ";
htmldef "qTop" as " qTop "; althtmldef "qTop" as " qTop ";
  latexdef "qTop" as "{\rm qTop}";
htmldef "Xs." as " <IMG SRC='times.gif' WIDTH=9 HEIGHT=19 ALT=' X.' " +
    "TITLE='X.'><sub><i>s</i></sub> ";
  althtmldef "Xs." as ' &times;<sub><i>s</i></sub> ';
  latexdef "Xs." as "\times_s";
htmldef "Cat" as
    "<IMG SRC='_cat.gif' WIDTH=24 HEIGHT=19 ALT=' Cat' TITLE='Cat'>";
  althtmldef "Cat" as "Cat";
  latexdef "Cat" as "{\rm Cat}";
htmldef "Id" as "<IMG SRC='_id.gif' WIDTH=12 HEIGHT=19 ALT=' Id' TITLE='Id'>";
  althtmldef "Id" as "Id";
  latexdef "Id" as "{\rm Id}";
htmldef "Homf" as
    " <IMG SRC='_hom.gif' WIDTH=27 HEIGHT=19 ALT=' Hom' TITLE='Hom'>" +
    "<sub><i>f</i></sub> ";
  althtmldef "Homf" as " Hom<sub><i>f</i></sub> ";
  latexdef "Homf" as "{\rm Hom}";
htmldef "comf" as "comp<sub><i>f</i></sub>";
  althtmldef "comf" as "comp<sub><i>f</i></sub>";
  latexdef "comf" as "{\rm comp}_f";
htmldef "oppCat" as "oppCat";
  althtmldef "oppCat" as "oppCat";
  latexdef "oppCat" as "{\rm oppCat}";
htmldef "Mono" as "Mono"; althtmldef "Mono" as "Mono";
  latexdef "Mono" as "{\rm Mono}";
htmldef "Epi" as "Epi"; althtmldef "Epi" as "Epi";
  latexdef "Epi" as "{\rm Epi}";
htmldef "Sect" as "Sect"; althtmldef "Sect" as "Sect";
  latexdef "Sect" as "{\rm Sect}";
htmldef "Inv" as "Inv"; althtmldef "Inv" as "Inv";
  latexdef "Inv" as "{\rm Inv}";
htmldef "Iso" as
    " <IMG SRC='_iso.gif' WIDTH=17 HEIGHT=19 ALT=' Iso' TITLE='Iso'> ";
  althtmldef "Iso" as "Iso";
  latexdef "Iso" as "{\rm Iso}";
htmldef "C_cat" as
    " <IMG SRC='subseteq.gif' WIDTH=12 HEIGHT=19 ALT=' C_' TITLE='C_'>" +
    "<SUB>cat</SUB> ";
  althtmldef "C_cat" as ' &#8838;<SUB>cat</SUB> '; /* &subE; */
  latexdef "C_cat" as "\subseteq_{cat}";
htmldef "|`cat" as " <IMG SRC='restriction.gif' WIDTH=5 HEIGHT=19 ALT=' |`'" +
    " TITLE='|`'><SUB>cat</SUB> ";
  althtmldef "|`cat" as " &#8638;<SUB>cat</SUB> ";
  latexdef "|`cat" as "\restriction_{cat}";
htmldef "Subcat" as "Subcat"; althtmldef "Subcat" as "Subcat";
  latexdef "Subcat" as "{\rm Subcat}";
htmldef "Func" as
    " <IMG SRC='_func.gif' WIDTH=32 HEIGHT=19 ALT=' Func' TITLE='Func'> ";
  althtmldef "Func" as " Func ";
  latexdef "Func" as " {\rm Func} ";
htmldef "idFunc" as "id<sub><i>func</i></sub>";
  althtmldef "idFunc" as "id<sub><i>func</i></sub>";
  latexdef "idFunc" as "{\rm id}_{func}";
htmldef "o.func" as
    " <IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' o.' TITLE='o.'>" +
    "<sub><i>func</i></sub> ";
  althtmldef "o.func" as ' &#8728;<sub><i>func</i></sub> ';
  latexdef "o.func" as "\circ_{func}";
htmldef "|`f" as " <IMG SRC='restriction.gif' WIDTH=5 HEIGHT=19 ALT=' |`'" +
    " TITLE='|`'><SUB><i>f</i></SUB> ";
  althtmldef "|`f" as " &#8638;<SUB><i>f</i></SUB> ";
  latexdef "|`f" as "\restriction_f";
htmldef "Full" as " Full "; althtmldef "Full" as " Full ";
  latexdef "Full" as "{\rm Full}";
htmldef "Faith" as " Faith "; althtmldef "Faith" as " Faith ";
  latexdef "Faith" as "{\rm Faith}";
htmldef "Nat" as " Nat "; althtmldef "Nat" as " Nat ";
  latexdef "Nat" as "{\rm Nat}";
htmldef "FuncCat" as " FuncCat "; althtmldef "FuncCat" as " FuncCat ";
  latexdef "FuncCat" as " {\rm FuncCat} ";
htmldef "DiagFunc" as "&Delta;<sub>func</sub>";
  althtmldef "DiagFunc" as "&Delta;<sub>func</sub>";
  latexdef "DiagFunc" as "\Delta_{func}";
htmldef "domA" as
    "<IMG SRC='_dom.gif' WIDTH=26 HEIGHT=19 ALT='dom' TITLE='dom'>" +
    "<IMG SRC='suba.gif' WIDTH=7 HEIGHT=19 ALT='A' TITLE='A'>";
  althtmldef "domA" as 'dom<sub><i>a</i></sub>';
  latexdef "domA" as "{\rm dom}_a";
htmldef "codA" as 'cod<sub><i>a</i></sub>';
  althtmldef "codA" as 'cod<sub><i>a</i></sub>';
  latexdef "codA" as "{\rm cod}_a";
htmldef "Arrow" as "Nat"; althtmldef "Arrow" as "Arrow";
  latexdef "Arrow" as "{\rm Arrow}";
htmldef "HomA" as 'Hom<sub><i>a</i></sub>';
  althtmldef "HomA" as 'Hom<sub><i>a</i></sub>';
  latexdef "HomA" as "{\rm Hom}_a";
htmldef "IdA" as 'Id<sub><i>a</i></sub>';
  althtmldef "IdA" as 'Id<sub><i>a</i></sub>';
  latexdef "IdA" as "{\rm Id}_a";
htmldef "compA" as 'comp<sub><i>a</i></sub>';
  althtmldef "compA" as 'comp<sub><i>a</i></sub>';
  latexdef "compA" as "{\rm comp}_a";
htmldef "SetCat" as
    "<IMG SRC='_setcat.gif' WIDTH=45 HEIGHT=19 ALT=' SetCat' TITLE='SetCat'>";
  althtmldef "SetCat" as "SetCat";
  latexdef "SetCat" as "{\rm SetCat}";
htmldef "CatCat" as "CatCat"; althtmldef "CatCat" as "CatCat";
  latexdef "CatCat" as "{\rm CatCat}";
htmldef "Xc." as " <IMG SRC='times.gif' WIDTH=9 HEIGHT=19 ALT=' X.' " +
    "TITLE='X.'><sub><i>c</i></sub> ";
  althtmldef "Xc." as ' &times;<sub><i>c</i></sub> ';
  latexdef "Xc." as "\times_c";
htmldef "1stF" as
    " <IMG SRC='_1st.gif' WIDTH=15 HEIGHT=19 ALT=' 1st' TITLE='1st'>" +
    "<sub><i>F</i></sub> ";
  althtmldef "1stF" as ' 1<SUP>st</SUP><sub><i>F</i></sub> ';
  latexdef "1stF" as " 1^{\rm st}{}_F ";
htmldef "2ndF" as
    " <IMG SRC='_2nd.gif' WIDTH=21 HEIGHT=19 ALT=' 2nd' TITLE='2nd'>" +
    "<sub><i>F</i></sub> ";
  althtmldef "2ndF" as ' 2<SUP>nd</SUP><sub><i>F</i></sub> ';
  latexdef "2ndF" as " 2^{\rm nd}{}_F ";
htmldef "pairF" as ' &lang;,&rang;<sub><i>F</i></sub> ';
  althtmldef "pairF" as ' &lang;,&rang;<sub><i>F</i></sub> ';
  latexdef "pairF" as " \langle,\rangle_F ";
htmldef "evalF" as ' eval<sub><i>F</i></sub> ';
  althtmldef "evalF" as ' eval<sub><i>F</i></sub> ';
  latexdef "evalF" as " {\rm eval}_F ";
htmldef "curryF" as ' curry<sub><i>F</i></sub> ';
  althtmldef "curryF" as ' curry<sub><i>F</i></sub> ';
  latexdef "curryF" as " {\rm curry}_F ";
htmldef "uncurryF" as ' uncurry<sub><i>F</i></sub> ';
  althtmldef "uncurryF" as ' uncurry<sub><i>F</i></sub> ';
  latexdef "uncurryF" as " {\rm uncurry}_F ";
htmldef "HomF" as 'Hom<sub><i>F</i></sub>';
  althtmldef "HomF" as 'Hom<sub><i>F</i></sub>';
  latexdef "HomF" as "{\rm Hom}_F";
htmldef "Yon" as "Yon"; althtmldef "Yon" as "Yon";
  latexdef "Yon" as "{\rm Yon}";
htmldef "Preset" as
   " <IMG SRC='_preset.gif' WIDTH=41 HEIGHT=19 ALT=' Preset' TITLE='Preset'> ";
  althtmldef "Preset" as " Preset ";
  latexdef "Preset" as "{\rm Preset}";
htmldef "Dirset" as "Dirset";
  althtmldef "Dirset" as "Dirset";
  latexdef "Dirset" as "\mathrm{Dirset}";
htmldef "Poset" as
    "<IMG SRC='_poset.gif' WIDTH=35 HEIGHT=19 ALT=' Poset' TITLE='Poset'>";
  althtmldef "Poset" as "Poset";
  latexdef "Poset" as "{\rm Poset}";
htmldef "lt" as
    "<IMG SRC='_rmlt.gif' WIDTH=10 HEIGHT=19 ALT=' lt' TITLE='lt'>";
  althtmldef "lt" as "lt";
  latexdef "lt" as "{\rm lt}";
htmldef "lub" as
    "<IMG SRC='_lub.gif' WIDTH=20 HEIGHT=19 ALT=' lub' TITLE='lub'>";
  althtmldef "lub" as "lub";
  latexdef "lub" as "{\rm lub}";
htmldef "glb" as
    "<IMG SRC='_glb.gif' WIDTH=20 HEIGHT=19 ALT=' glb' TITLE='glb'>";
  althtmldef "glb" as "glb";
  latexdef "glb" as "{\rm glb}";
htmldef "join" as
    "<IMG SRC='_join.gif' WIDTH=25 HEIGHT=19 ALT=' join' TITLE='join'>";
  althtmldef "join" as "join";
  latexdef "join" as "{\rm join}";
htmldef "meet" as
    "<IMG SRC='_meet.gif' WIDTH=32 HEIGHT=19 ALT=' meet' TITLE='meet'>";
  althtmldef "meet" as "meet";
  latexdef "meet" as "{\rm meet}";
htmldef "Toset" as "Toset";
  althtmldef "Toset" as "Toset";
  latexdef "Toset" as "{\rm Toset}";
htmldef "1." as
    "<IMG SRC='_1dot.gif' WIDTH=10 HEIGHT=19 ALT=' 1.' TITLE='1.'>";
  althtmldef "1." as "1.";
  latexdef "1." as "1.";
htmldef "0." as
    "<IMG SRC='_0dot.gif' WIDTH=11 HEIGHT=19 ALT=' 0.' TITLE='0.'>";
  althtmldef "0." as "0.";
  latexdef "0." as "0.";
htmldef "Lat" as
    "<IMG SRC='_lat.gif' WIDTH=23 HEIGHT=19 ALT=' Lat' TITLE='Lat'>";
  althtmldef "Lat" as "Lat";
  latexdef "Lat" as "{\rm Lat}";
htmldef "CLat" as
    "<IMG SRC='_clat.gif' WIDTH=33 HEIGHT=19 ALT=' CLat' TITLE='CLat'>";
  althtmldef "CLat" as "CLat";
  latexdef "CLat" as "{\rm CLat}";
htmldef "ODual" as "ODual";
  althtmldef "ODual" as "ODual";
  latexdef "ODual" as "\mathrm{ODual}";
htmldef "toInc" as "toInc";
  althtmldef "toInc" as "toInc";
  latexdef "toInc" as "\mathrm{toInc}";
htmldef "DLat" as "DLat";
  althtmldef "DLat" as "DLat";
  latexdef "DLat" as "\mathrm{DLat}";
htmldef "PosetRel" as
    "<IMG SRC='_posetrel.gif' WIDTH=56 HEIGHT=19 " +
    "ALT=' PosetRel' TITLE='PosetRel'>";
  althtmldef "PosetRel" as "PosetRel";
  latexdef "PosetRel" as "{\rm PosetRel}";
htmldef "TosetRel" as " <IMG SRC='_tosetrel.gif' WIDTH=55 HEIGHT=19 " +
    "ALT=' TosetRel' TITLE='TosetRel'> ";
  althtmldef "TosetRel" as " TosetRel ";
  latexdef "TosetRel" as "{\rm TosetRel}";
/* obsolete as of 28-Aug-2018.  -NM
htmldef "supw" as
    " <IMG SRC='_sup.gif' WIDTH=22 HEIGHT=19 ALT=' sup' TITLE='sup'>" +
    "<IMG SRC='subrmw.gif' WIDTH=10 HEIGHT=19 ALT=' w' TITLE='w'> ";
  althtmldef "supw" as " sup<SUB>w</SUB> ";
  latexdef "supw" as "{\rm sup}_{\rm w}";
htmldef "infw" as
    " <IMG SRC='_inf.gif' WIDTH=18 HEIGHT=19 ALT=' inf' TITLE='inf'>" +
    "<IMG SRC='subrmw.gif' WIDTH=10 HEIGHT=19 ALT=' w' TITLE='w'> ";
  althtmldef "infw" as " inf<SUB>w</SUB> ";
  latexdef "infw" as "{\rm inf}_{\rm w}";
htmldef "LatRel" as
    "<IMG SRC='_latrel.gif' WIDTH=44 HEIGHT=19 ALT=' LatRel' TITLE='LatRel'>";
  althtmldef "LatRel" as "LatRel";
  latexdef "LatRel" as "{\rm LatRel}";
*/
htmldef "DirRel" as
    "<IMG SRC='_dirrel.gif' WIDTH=41 HEIGHT=19 ALT=' DirRel' TITLE='DirRel'>";
  althtmldef "DirRel" as "DirRel";
  latexdef "DirRel" as "{\rm DirRel}";
htmldef "tail" as
    "<IMG SRC='_tail.gif' WIDTH=22 HEIGHT=19 ALT=' tail' TITLE='tail'>";
  althtmldef "tail" as "tail";
  latexdef "tail" as "{\rm tail}";
htmldef "Mnd" as
    "<IMG SRC='_mnd.gif' WIDTH=28 HEIGHT=19 ALT=' Mnd' TITLE='Mnd'>";
  althtmldef "Mnd" as "Mnd";
  latexdef "Mnd" as "{\rm Mnd}";
htmldef "Grp" as
    "<IMG SRC='_grp.gif' WIDTH=25 HEIGHT=19 ALT=' Grp' TITLE='Grp'>";
  althtmldef "Grp" as "Grp";
  latexdef "Grp" as "{\rm Grp}";
htmldef "invg" as "<IMG SRC='_inv.gif' WIDTH=19 HEIGHT=19 ALT=' inv' " +
    "TITLE='inv'><IMG SRC='subg.gif' WIDTH=7 HEIGHT=19 ALT=' g' TITLE='g'>";
  althtmldef "invg" as "inv<SUB>g</SUB>";
  latexdef "invg" as "{\rm inv}_{\rm g}";
htmldef "+f" as "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT=' f' TITLE='f'>";
  althtmldef "+f" as '+<SUB>&#x1D453;</SUB>';
  latexdef "+f" as "+_f";
htmldef "-g" as
    "<IMG SRC='_minusg.gif' WIDTH=17 HEIGHT=19 ALT=' -g' TITLE='-g'>";
  althtmldef "-g" as "-<SUB>g</SUB>";
  latexdef "-g" as "-_{\rm g}";
htmldef ".g" as ".<SUB>g</SUB>";
  althtmldef ".g" as ".<SUB>g</SUB>";
  latexdef ".g" as "\cdot_{\rm g}";
htmldef "MndHom" as " MndHom "; althtmldef "MndHom" as " MndHom ";
  latexdef "MndHom" as " {\rm MndHom} ";
htmldef "SubMnd" as "SubMnd"; althtmldef "SubMnd" as "SubMnd";
  latexdef "SubMnd" as "{\rm SubMnd}";
htmldef "Word" as "Word ";
  althtmldef "Word" as "Word ";
  latexdef "Word" as "\mathrm{Word }";
htmldef "concat" as " concat ";
  althtmldef "concat" as " concat ";
  latexdef "concat" as "\mathrm{ concat }";
htmldef '<"' as
    "<IMG SRC='langle.gif' WIDTH=4 HEIGHT=19 ALT=' &lt;' TITLE='&lt;'>" +
    "<IMG SRC='backquote.gif' WIDTH=7 HEIGHT=19 ALT='" + '"' +
      "' TITLE='" + '"' + "'>";
  althtmldef '<"' as '&lang;&ldquo;'; /* &#9001;&#8220; */
  latexdef '<"' as "\langle``";
htmldef '">' as
    "<IMG SRC='quote.gif' WIDTH=7 HEIGHT=19 ALT=' " + '"' +
      "' TITLE='" + '"' + "'>" +
    "<IMG SRC='rangle.gif' WIDTH=4 HEIGHT=19 ALT='&gt;' TITLE='&gt;'>";
  althtmldef '">' as '&rdquo;&rang;'; /* &#8221;&#9002; */
  latexdef '">' as "''\rangle";
htmldef "substr" as " substr ";
  althtmldef "substr" as " substr ";
  latexdef "substr" as "\mathrm{ substr }";
htmldef "splice" as " splice ";
  althtmldef "splice" as " splice ";
  latexdef "splice" as "\mathrm{ splice }";
htmldef "reverse" as "reverse";
  althtmldef "reverse" as "reverse";
  latexdef "reverse" as "\mathrm{reverse}";
htmldef "freeMnd" as "freeMnd"; althtmldef "freeMnd" as "freeMnd";
  latexdef "freeMnd" as "{\rm freeMnd}";
htmldef "varFMnd" as "var<SUB><I>FMnd</I></SUB>";
  althtmldef "varFMnd" as "var<SUB><I>FMnd</I></SUB>";
  latexdef "varFMnd" as "{\rm var}_{FMnd}";
htmldef "~QG" as " ~<sub><i>QG</i></sub> ";
  althtmldef "~QG" as " ~<sub><i>QG</i></sub> ";
  latexdef "~QG" as " \sim_{QG} ";
htmldef "SubGrp" as "SubGrp"; althtmldef "SubGrp" as "SubGrp";
  latexdef "SubGrp" as "{\rm SubGrp}";
htmldef "NrmSGrp" as "NrmSGrp"; althtmldef "NrmSGrp" as "NrmSGrp";
  latexdef "NrmSGrp" as "{\rm NrmSGrp}";
htmldef "GrpHom" as
   " <IMG SRC='_grphom.gif' WIDTH=54 HEIGHT=19 ALT=' GrpHom' TITLE='GrpHom'> ";
  althtmldef "GrpHom" as " GrpHom ";
  latexdef "GrpHom" as "{\rm GrpHom}";
htmldef "GrpIso" as " GrpIso ";
  althtmldef "GrpIso" as " GrpIso ";
  latexdef "GrpIso" as "{\rm GrpIso}";
htmldef "~=g" as " <IMG SRC='simeq.gif' WIDTH=26 HEIGHT=19 " +
    "ALT=' ~=ph' TITLE='~=ph'><SUB>&#x1D454;</SUB> ";
  althtmldef "~=g" as " &#8771;<SUB>&#x1D454;</SUB> ";
  latexdef "~=g" as "\simeq_{g}";
htmldef "GrpAct" as
   " <IMG SRC='_grpact.gif' WIDTH=48 HEIGHT=19 ALT=' GrpAct' TITLE='GrpAct'> ";
  althtmldef "GrpAct" as " GrpAct ";
  latexdef "GrpAct" as "{\rm GrpAct}";
htmldef "SymGrp" as
    "<IMG SRC='_symgrp.gif' WIDTH=53 HEIGHT=19 ALT=' SymGrp' TITLE='SymGrp'>";
  althtmldef "SymGrp" as "SymGrp";
  latexdef "SymGrp" as "{\rm SymGrp}";
htmldef "od" as "<IMG SRC='_od.gif' WIDTH=15 HEIGHT=19 ALT=' od' TITLE='od'>";
  althtmldef "od" as "od";
  latexdef "od" as "\rm{od}";
htmldef "gEx" as "gEx";
  althtmldef "gEx" as "gEx";
  latexdef "gEx" as "{\rm gEx}";
htmldef "pGrp" as " pGrp ";
  althtmldef "pGrp" as " pGrp ";
  latexdef "pGrp" as "{\rm pGrp}";
htmldef "pSyl" as " pSyl ";
  althtmldef "pSyl" as " pSyl ";
  latexdef "pSyl" as "{\rm pSyl}";
htmldef "~FG" as " ~<sub><i>FG</i></sub> ";
  althtmldef "~FG" as " ~<sub><i>FG</i></sub> ";
  latexdef "~FG" as " \sim_{FG} ";
htmldef "freeGrp" as "freeGrp"; althtmldef "freeGrp" as "freeGrp";
  latexdef "freeGrp" as "{\rm freeGrp}";
htmldef "varFGrp" as "var<SUB><I>FGrp</I></SUB>";
  althtmldef "varFGrp" as "var<SUB><I>FGrp</I></SUB>";
  latexdef "varFGrp" as "{\rm var}_{FGrp}";
htmldef "CMnd" as "CMnd";
  althtmldef "CMnd" as "CMnd";
  latexdef "CMnd" as "{\rm CMnd}";
htmldef "CycGrp" as "CycGrp";
  althtmldef "CycGrp" as "CycGrp";
  latexdef "CycGrp" as "{\rm CycGrp}";
htmldef "DProd" as " DProd ";
  althtmldef "DProd" as " DProd ";
  latexdef "DProd" as "{\rm DProd }";
htmldef "dProj" as "dProj";
  althtmldef "dProj" as "dProj";
  latexdef "dProj" as "{\rm dProj}";
htmldef "Abel" as
    "<IMG SRC='_abel.gif' WIDTH=28 HEIGHT=19 ALT=' Abel' TITLE='Abel'>";
  althtmldef "Abel" as "Abel";
  latexdef "Abel" as "{\rm Abel}";
htmldef "oppG" as "opp<sub><i>g</i></sub>";
  althtmldef "oppG" as "opp<sub><i>g</i></sub>";
  latexdef "oppG" as "{\rm opp}_g";
htmldef "mulGrp" as "mulGrp";
  althtmldef "mulGrp" as "mulGrp";
  latexdef "mulGrp" as "{\rm mulGrp}";
htmldef "Ring" as
    "<IMG SRC='_ring.gif' WIDTH=30 HEIGHT=19 ALT=' Ring' TITLE='Ring'>";
  althtmldef "Ring" as "Ring";
  latexdef "Ring" as "{\rm Ring}";
htmldef "CRing" as
    "<IMG SRC='_cring.gif' WIDTH=40 HEIGHT=19 ALT=' CRing' TITLE='CRing'>";
  althtmldef "CRing" as "CRing";
  latexdef "CRing" as "{\rm CRing}";
htmldef "1r" as "<IMG SRC='_1r.gif' WIDTH=13 HEIGHT=19 ALT=' 1r' TITLE='1r'>";
  althtmldef "1r" as "1<SUB>r</SUB>";
  latexdef "1r" as "1_{\rm r}{\rm }";
htmldef "oppR" as "opp<sub><i>r</i></sub>";
  althtmldef "oppR" as "opp<sub><i>r</i></sub>";
  latexdef "oppR" as "{\rm opp}_r";
htmldef "||r" as "<IMG SRC='parallel.gif' WIDTH=5 HEIGHT=19 ALT=' ||' " +
    "TITLE='||'><sub><i>r</i></sub>";
  althtmldef "||r" as "&#8741;<sub><i>r</i></sub>";
  latexdef "||r" as "\parallel_r";
htmldef "Unit" as "Unit"; althtmldef "Unit" as "Unit";
  latexdef "Unit" as "{\rm Unit}";
htmldef "Irred" as "Irred"; althtmldef "Irred" as "Irred";
  latexdef "Irred" as "{\rm Irred}";
htmldef "invr" as
    "<IMG SRC='_invr.gif' WIDTH=23 HEIGHT=19 ALT=' invr' TITLE='invr'>";
  althtmldef "invr" as "inv<SUB>r</SUB>";
  latexdef "invr" as "{\rm inv}_r";
htmldef "/r" as "/<SUB>r</SUB>";
  althtmldef "/r" as "/<SUB>r</SUB>";
  latexdef "/r" as "/_r";
htmldef "RingHom" as " RingHom "; althtmldef "RingHom" as " RingHom ";
  latexdef "RingHom" as " {\rm RingHom} ";
htmldef "RingIso" as " RingIso "; althtmldef "RingIso" as " RingIso ";
  latexdef "RingIso" as " {\rm RingIso} ";
htmldef "DivRing" as
  "<IMG SRC='_divring.gif' WIDTH=52 HEIGHT=19 ALT=' DivRing' TITLE='DivRing'>";
  althtmldef "DivRing" as "DivRing";
  latexdef "DivRing" as "{\rm DivRing}";
htmldef "Field" as "Field";
  althtmldef "Field" as "Field";
  latexdef "Field" as "\mathrm{Field}";
htmldef "SubRing" as "SubRing"; althtmldef "SubRing" as "SubRing";
  latexdef "SubRing" as "{\rm SubRing}";
htmldef "RingSpan" as "RingSpan";
  althtmldef "RingSpan" as "RingSpan";
  latexdef "RingSpan" as "{\rm RingSpan}";
htmldef "AbsVal" as "AbsVal";
  althtmldef "AbsVal" as "AbsVal";
  latexdef "AbsVal" as "{\rm AbsVal}";
htmldef "*Ring" as "<IMG SRC='_astring.gif' " +
    "WIDTH=41 HEIGHT=19 ALT=' *Ring' TITLE='*Ring'>";
  althtmldef "*Ring" as "*-Ring";
  latexdef "*Ring" as "\ast{\rm -Ring}";
htmldef "*rf" as "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT=' *' TITLE='*'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT=' r' TITLE='r'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT=' f' TITLE='f'>";
  althtmldef "*rf" as "*<SUB><I>rf</I></SUB>";
  latexdef "*rf" as "\ast_{rf}";
htmldef "LMod" as
    "<IMG SRC='_lmod.gif' WIDTH=36 HEIGHT=19 ALT=' LMod' TITLE='LMod'>";
  althtmldef "LMod" as "LMod";
  latexdef "LMod" as "{\rm LMod}";
htmldef ".sf" as
    "<IMG SRC='_cds.gif' WIDTH=9 HEIGHT=19 ALT=' .s' TITLE='.s'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT=' f' TITLE='f'>";
  althtmldef ".sf" as ' <B>&middot;</B><SUB><I>sf</I></SUB> ';
  latexdef ".sf" as '\cdot_{sf}';
htmldef "LSubSp" as
    "<IMG SRC='_lsubsp.gif' WIDTH=49 HEIGHT=19 ALT=' LSubSp' TITLE='LSubSp'>";
  althtmldef "LSubSp" as "LSubSp";
  latexdef "LSubSp" as "{\rm LSubSp}";
htmldef "LSpan" as
    "<IMG SRC='_lspan.gif' WIDTH=41 HEIGHT=19 ALT=' LSpan' TITLE='LSpan'>";
  althtmldef "LSpan" as "LSpan";
  latexdef "LSpan" as "{\rm LSpan}";
htmldef "LMHom" as " LMHom ";
  althtmldef "LMHom" as " LMHom ";
  latexdef "LMHom" as "{\rm LMHom}";
htmldef "LMIso" as " LMIso ";
  althtmldef "LMIso" as " LMIso ";
  latexdef "LMIso" as "{\rm LMIso}";
htmldef "~=m" as " <IMG SRC='simeq.gif' WIDTH=26 HEIGHT=19 " +
    "ALT=' ~=ph' TITLE='~=ph'><SUB>&#x1D45A;</SUB> ";
  althtmldef "~=m" as " &#8771;<SUB>&#x1D45A;</SUB> ";
  latexdef "~=m" as "\simeq_{m}";
htmldef "LBasis" as "LBasis";
  althtmldef "LBasis" as "LBasis";
  latexdef "LBasis" as "{\rm LBasis}";
htmldef "LSSum" as
    "<IMG SRC='_lssum.gif' WIDTH=45 HEIGHT=19 ALT=' LSSum' TITLE='LSSum'>";
  althtmldef "LSSum" as "LSSum";
  latexdef "LSSum" as "{\rm LSSum}";
htmldef "proj1" as
    "<IMG SRC='_proj.gif' WIDTH=24 HEIGHT=19 ALT=' proj' TITLE='proj'>" +
    "<IMG SRC='sub1.gif' WIDTH=4 HEIGHT=19 ALT=' 1' TITLE='1'>";
  althtmldef "proj1" as 'proj<SUB>1</SUB>';
  latexdef "proj1" as '{\rm proj}_1';
htmldef "LVec" as
    "<IMG SRC='_lvec.gif' WIDTH=33 HEIGHT=19 ALT=' LVec' TITLE='LVec'>";
  althtmldef "LVec" as "LVec";
  latexdef "LVec" as "{\rm LVec}";
htmldef "subringAlg" as " subringAlg ";
  althtmldef "subringAlg" as " subringAlg ";
  latexdef "subringAlg" as "{\rm subringAlg}";
htmldef "ringLMod" as "ringLMod";
  althtmldef "ringLMod" as "ringLMod";
  latexdef "ringLMod" as "{\rm ringLMod}";
htmldef "RSpan" as "RSpan"; althtmldef "RSpan" as "RSpan";
  latexdef "RSpan" as "{\rm RSpan}";
htmldef "LIdeal" as "LIdeal";
  althtmldef "LIdeal" as "LIdeal";
  latexdef "LIdeal" as "{\rm LIdeal}";
htmldef "2Ideal" as "2Ideal";
  althtmldef "2Ideal" as "2Ideal";
  latexdef "2Ideal" as "{\rm 2Ideal}";
htmldef "LPIdeal" as "LPIdeal";
  althtmldef "LPIdeal" as "LPIdeal";
  latexdef "LPIdeal" as "{\rm LPIdeal}";
/*
htmldef "Top1c" as "Top1c";
  althtmldef "Top1c" as "Top1c";
  latexdef "Top1c" as "{\rm Top1c}";
htmldef "Top2c" as "Top2c";
  althtmldef "Top2c" as "Top2c";
  latexdef "Top2c" as "{\rm Top2c}";
*/
htmldef "LPIR" as "LPIR";
  althtmldef "LPIR" as "LPIR";
  latexdef "LPIR" as "{\rm LPIR}";
htmldef "NzRing" as "NzRing";
  althtmldef "NzRing" as "NzRing";
  latexdef "NzRing" as "{\rm NzRing}";
htmldef "RLReg" as "RLReg";
  althtmldef "RLReg" as "RLReg";
  latexdef "RLReg" as "\mathrm{RLReg}";
htmldef "Domn" as "Domn";
  althtmldef "Domn" as "Domn";
  latexdef "Domn" as "\mathrm{Domn}";
htmldef "IDomn" as "IDomn";
  althtmldef "IDomn" as "IDomn";
  latexdef "IDomn" as "\mathrm{IDomn}";
htmldef "PID" as "PID";
  althtmldef "PID" as "PID";
  latexdef "PID" as "\mathrm{PID}";
htmldef "AssAlg" as "AssAlg"; althtmldef "AssAlg" as "AssAlg";
  latexdef "AssAlg" as "{\rm AssAlg}";
htmldef "AlgSpan" as "AlgSpan"; althtmldef "AlgSpan" as "AlgSpan";
  latexdef "AlgSpan" as "{\rm AlgSpan}";
htmldef "algSc" as "algSc";
  althtmldef "algSc" as "algSc";
  latexdef "algSc" as "{\rm algSc}";
htmldef "mPwSer" as " mPwSer "; althtmldef "mPwSer" as " mPwSer ";
  latexdef "mPwSer" as " {\rm mPwSer} ";
htmldef "mVar" as " mVar "; althtmldef "mVar" as " mVar ";
  latexdef "mVar" as " {\rm mVar} ";
htmldef "mPoly" as " mPoly "; althtmldef "mPoly" as " mPoly ";
  latexdef "mPoly" as " {\rm mPoly} ";
htmldef "evalSub" as " evalSub "; althtmldef "evalSub" as " evalSub ";
  latexdef "evalSub" as " {\rm evalSub} ";
htmldef "eval" as " eval "; althtmldef "eval" as " eval ";
  latexdef "eval" as " {\rm eval} ";
htmldef "mHomP" as " mHomP "; althtmldef "mHomP" as " mHomP ";
  latexdef "mHomP" as " {\rm mHomP} ";
htmldef "mPSDer" as " mPSDer "; althtmldef "mPSDer" as " mPSDer ";
  latexdef "mPSDer" as " {\rm mPSDer} ";
htmldef "<bag" as " <IMG SRC='lt.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;' " +
    "TITLE='&lt;'><sub>bag</sub> ";
  althtmldef "<bag" as " &lt;<sub>bag</sub> ";
  latexdef "<bag" as "<_{\rm bag}";
htmldef "ordPwSer" as " ordPwSer "; althtmldef "ordPwSer" as " ordPwSer ";
  latexdef "ordPwSer" as "{\rm ordPwSer}";
htmldef "selectVars" as " selectVars ";
  althtmldef "selectVars" as " selectVars ";
  latexdef "selectVars" as " {\rm selectVars} ";
htmldef "mDeg" as " mDeg "; althtmldef "mDeg" as " mDeg ";
  latexdef "mDeg" as " {\rm mDeg} ";
htmldef "AlgInd" as " AlgInd "; althtmldef "AlgInd" as " AlgInd ";
  latexdef "AlgInd" as " {\rm AlgInd} ";
htmldef "PwSer1" as "PwSer<sub>1</sub>";
  althtmldef "PwSer1" as "PwSer<sub>1</sub>";
  latexdef "PwSer1" as "{\rm PwSer}_1";
htmldef "var1" as "var<sub>1</sub>"; althtmldef "var1" as "var<sub>1</sub>";
  latexdef "var1" as "{\rm var}_1";
htmldef "Poly1" as "Poly<sub>1</sub>";
  althtmldef "Poly1" as "Poly<sub>1</sub>";
  latexdef "Poly1" as "{\rm Poly}_1";
htmldef "evalSub1" as " evalSub<sub>1</sub> ";
  althtmldef "evalSub1" as " evalSub<sub>1</sub> ";
  latexdef "evalSub1" as " {\rm evalSub}_1 ";
htmldef "eval1" as "eval<sub>1</sub>";
  althtmldef "eval1" as "eval<sub>1</sub>";
  latexdef "eval1" as "{\rm eval}_1";
htmldef "deg1" as " deg<sub>1</sub> ";
  althtmldef "deg1" as " deg<sub>1</sub> ";
  latexdef "deg1" as " {\rm deg}_1 ";
htmldef "coe1" as "coe<sub>1</sub>"; althtmldef "coe1" as "coe<sub>1</sub>";
  latexdef "coe1" as "{\rm coe}_1";
htmldef "toPoly1" as "toPoly<sub>1</sub>";
  althtmldef "toPoly1" as "toPoly<sub>1</sub>";
  latexdef "toPoly1" as "{\rm toPoly}_1";
htmldef "*Met" as
    "<IMG SRC='infty.gif' WIDTH=17 HEIGHT=19 ALT=' *' TITLE='*'>" +
    "<IMG SRC='_met.gif' WIDTH=25 HEIGHT=19 ALT=' Met' TITLE='Met'>";
  althtmldef "*Met" as "&infin;Met";
  latexdef "*Met" as "\infty{\rm Met}";
htmldef "Met" as
    "<IMG SRC='_met.gif' WIDTH=25 HEIGHT=19 ALT=' Met' TITLE='Met'>";
  althtmldef "Met" as "Met";
  latexdef "Met" as "{\rm Met}";
htmldef "ball" as
    "<IMG SRC='_ball.gif' WIDTH=24 HEIGHT=19 ALT=' ball' TITLE='ball'>";
  althtmldef "ball" as "ball";
  latexdef "ball" as "{\rm ball}";
htmldef "MetOpen" as
  "<IMG SRC='_metopen.gif' WIDTH=59 HEIGHT=19 ALT=' MetOpen' TITLE='MetOpen'>";
  althtmldef "MetOpen" as "MetOpen";
  latexdef "MetOpen" as "{\rm MetOpen}";
htmldef "CCfld" as "&#8450;<SUB>fld</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "CCfld" as "&#8450;<SUB>fld</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "CCfld" as "{\rm CCfld}";
htmldef "ZRHom" as
    "<IMG SRC='bbz.gif' WIDTH=13 HEIGHT=19 ALT=' Z' TITLE='Z'>RHom";
  althtmldef "ZRHom" as "&#8484;RHom";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "ZRHom" as "{\rm ZRHom}";
htmldef "ZMod" as
    "<IMG SRC='bbz.gif' WIDTH=13 HEIGHT=19 ALT=' Z' TITLE='Z'>Mod";
  althtmldef "ZMod" as "&#8484;Mod";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "ZMod" as "{\rm ZMod}";
htmldef "chr" as "chr";
  althtmldef "chr" as "chr";
  latexdef "chr" as "\mathrm{chr}";
htmldef "Z/nZ" as "&#8484;/<i>n</i>&#8484;";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "Z/nZ" as "&#8484;/<i>n</i>&#8484;";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Z/nZ" as "{\rm Z/nZ}";
htmldef "PreHil" as
    "<IMG SRC='_prehil.gif' WIDTH=40 HEIGHT=19 ALT=' PreHil' TITLE='PreHil'>";
  althtmldef "PreHil" as "PreHil";
  latexdef "PreHil" as "{\rm PreHil}";
htmldef ".if" as
    "<IMG SRC='_cdi.gif' WIDTH=7 HEIGHT=19 ALT=' .i' TITLE='.i'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT=' f' TITLE='f'>";
  althtmldef ".if" as '<B>&middot;</B><SUB><I>if</I></SUB>';
  latexdef ".if" as '\cdot_{if}';
htmldef "ocv" as
    "<IMG SRC='_ocv.gif' WIDTH=22 HEIGHT=19 ALT=' ocv' TITLE='ocv'>";
  althtmldef "ocv" as "ocv";
  latexdef "ocv" as "{\rm ocv}";
htmldef "CSubSp" as
    "<IMG SRC='_csubsp.gif' WIDTH=50 HEIGHT=19 ALT=' CSubSp' TITLE='CSubSp'>";
  althtmldef "CSubSp" as "CSubSp";
  latexdef "CSubSp" as "{\rm CSubSp}";
htmldef "toHL" as "toHL"; althtmldef "toHL" as "toHL";
  latexdef "toHL" as "{\rm toHL}";
htmldef "proj" as
    "<IMG SRC='_proj.gif' WIDTH=24 HEIGHT=19 ALT=' proj' TITLE='proj'>";
  althtmldef "proj" as 'proj';
  latexdef "proj" as '{\rm proj}';
htmldef "Hil" as
    "<IMG SRC='_hil.gif' WIDTH=18 HEIGHT=19 ALT=' Hil' TITLE='Hil'>";
  althtmldef "Hil" as "Hil";
  latexdef "Hil" as "{\rm Hil}";
htmldef "OBasis" as "OBasis"; althtmldef "OBasis" as "OBasis";
  latexdef "OBasis" as "{\rm OBasis}";
htmldef "Moore" as "Moore";
  althtmldef "Moore" as "Moore";
  latexdef "Moore" as "\mathrm{Moore}";
htmldef "mrCls" as "mrCls";
  althtmldef "mrCls" as "mrCls";
  latexdef "mrCls" as "\mathrm{mrCls}";
htmldef "mrInd" as "mrInd";
  althtmldef "mrInd" as "mrInd";
  latexdef "mrInd" as "\mathrm{mrInd}";
htmldef "ACS" as "ACS";
  althtmldef "ACS" as "ACS";
  latexdef "ACS" as "\mathrm{ACS}";
htmldef "Top" as
    "<IMG SRC='_top.gif' WIDTH=23 HEIGHT=19 ALT=' Top' TITLE='Top'>";
  althtmldef "Top" as "Top";
  latexdef "Top" as "{\rm Top}";
htmldef "TopOn" as "TopOn";
  althtmldef "TopOn" as "TopOn";
  latexdef "TopOn" as "\mathrm{TopOn}";
htmldef "TopSpOLD" as
    "<IMG SRC='_topsp.gif' WIDTH=41 HEIGHT=19 ALT=' TopSp' TITLE='TopSp'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "TopSpOLD" as "TopSp<SUB>OLD</SUB>";
  latexdef "TopSpOLD" as "{\rm TopSp_{OLD}}";
htmldef "TopSp" as
    "<IMG SRC='_topsp.gif' WIDTH=41 HEIGHT=19 ALT=' TopSp' TITLE='TopSp'>";
  althtmldef "TopSp" as "TopSp";
  latexdef "TopSp" as "{\rm TopSp}";
htmldef "TopBases" as
    "<IMG SRC='_topbases.gif' WIDTH=59 HEIGHT=19 " +
    "ALT=' TopBases' TITLE='TopBases'>";
  althtmldef "TopBases" as "TopBases";
  latexdef "TopBases" as "{\rm TopBases}";
htmldef "int" as
    "<IMG SRC='_int.gif' WIDTH=18 HEIGHT=19 ALT=' int' TITLE='int'>";
  althtmldef "int" as "int";
  latexdef "int" as "{\rm int}";
htmldef "cls" as
    "<IMG SRC='_cls.gif' WIDTH=17 HEIGHT=19 ALT=' cls' TITLE='cls'>";
  althtmldef "cls" as "cls";
  latexdef "cls" as "{\rm cls}";
htmldef "Clsd" as
    "<IMG SRC='_clsd.gif' WIDTH=28 HEIGHT=19 ALT=' Clsd' TITLE='Clsd'>";
  althtmldef "Clsd" as "Clsd";
  latexdef "Clsd" as "{\rm Clsd}";
htmldef "nei" as
    "<IMG SRC='_nei.gif' WIDTH=19 HEIGHT=19 ALT=' nei' TITLE='nei'>";
  althtmldef "nei" as "nei";
  latexdef "nei" as "{\rm nei}";
htmldef "limPt" as
    "<IMG SRC='_limpt.gif' WIDTH=35 HEIGHT=19 ALT=' limPt' TITLE='limPt'>";
  althtmldef "limPt" as "limPt";
  latexdef "limPt" as "{\rm limPt}";
htmldef "Perf" as "Perf";
  althtmldef "Perf" as "Perf";
  latexdef "Perf" as "{\rm Perf}";
htmldef "Cn" as
    " <IMG SRC='_cnf.gif' WIDTH=18 HEIGHT=19 ALT=' Cn' TITLE='Cn'> ";
  althtmldef "Cn" as " Cn ";
  latexdef "Cn" as "{\rm Cn}";
htmldef "CnP" as
    " <IMG SRC='_cnp.gif' WIDTH=27 HEIGHT=19 ALT=' CnP' TITLE='CnP'> ";
  althtmldef "CnP" as " CnP ";
  latexdef "CnP" as "{\rm CnP}";
htmldef "~~>t" as "<IMG SRC='rightsquigarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' ~~&gt;' TITLE='~~&gt;'>" +
    "<IMG SRC='subt.gif' WIDTH=5 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "~~>t" as
    "&#8669;<SUB>&#x1D461;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~~>t" as "\rightsquigarrow_t";
htmldef "Kol2" as
    "<IMG SRC='_kol2.gif' WIDTH=27 HEIGHT=19 ALT=' Kol2' TITLE='Kol2'>";
  althtmldef "Kol2" as "Kol2";
  latexdef "Kol2" as "{\rm Kol2}";
htmldef "Fre" as
    "<IMG SRC='_fre.gif' WIDTH=22 HEIGHT=19 ALT=' Fre' TITLE='Fre'>";
  althtmldef "Fre" as "Fre";
  latexdef "Fre" as "{\rm Fre}";
htmldef "Haus" as
    "<IMG SRC='_haus.gif' WIDTH=32 HEIGHT=19 ALT=' Haus' TITLE='Haus'>";
  althtmldef "Haus" as "Haus";
  latexdef "Haus" as "{\rm Haus}";
htmldef "Reg" as
    "<IMG SRC='_reg.gif' WIDTH=25 HEIGHT=19 ALT=' Reg' TITLE='Reg'>";
  althtmldef "Reg" as "Reg";
  latexdef "Reg" as "{\rm Reg}";
htmldef "Nrm" as
    "<IMG SRC='_nrm.gif' WIDTH=28 HEIGHT=19 ALT=' Nrm' TITLE='Nrm'>";
  althtmldef "Nrm" as "Nrm";
  latexdef "Nrm" as "{\rm Nrm}";
htmldef "CNrm" as "CNrm"; althtmldef "CNrm" as "CNrm";
  latexdef "CNrm" as "{\rm CNrm}";
htmldef "PNrm" as "PNrm"; althtmldef "PNrm" as "PNrm";
  latexdef "PNrm" as "{\rm PNrm}";
htmldef "Comp" as
    "<IMG SRC='_comp.gif' WIDTH=37 HEIGHT=19 ALT=' Comp' TITLE='Comp'>";
  althtmldef "Comp" as "Comp";
  latexdef "Comp" as "{\rm Comp}";
htmldef "Con" as
    "<IMG SRC='_con.gif' WIDTH=25 HEIGHT=19 ALT=' Con' TITLE='Con'>";
  althtmldef "Con" as "Con";
  latexdef "Con" as "{\rm Con}";
htmldef "1stc" as "<IMG SRC='_1stc.gif' WIDTH=25 HEIGHT=19 ALT=' 1stc'" +
    " TITLE='1stc'>";
  althtmldef "1stc" as "1<SUP>st</SUP>&#x1D714;"; /* math italic omega */
  latexdef "1stc" as "1^{\rm st}\omega";
htmldef "2ndc" as "<IMG SRC='_2ndc.gif' WIDTH=31 HEIGHT=19 ALT=' 2ndc'" +
    " TITLE='2ndc'>";
  althtmldef "2ndc" as "2<SUP>nd</SUP>&#x1D714;";
  latexdef "2ndc" as "2^{\rm nd}\omega";
htmldef "Locally" as "Locally "; althtmldef "Locally" as "Locally ";
  latexdef "Locally" as "{\rm Locally}";
htmldef "N-Locally" as "&#x1D45B;Locally ";
  althtmldef "N-Locally" as "&#x1D45B;-Locally ";
  latexdef "N-Locally" as "n\mbox{-Locally}";
htmldef "kGen" as "&#x1D458;Gen"; althtmldef "kGen" as "&#x1D458;Gen";
  latexdef "kGen" as "k{\rm Gen}";
htmldef "tX" as
    " <IMG SRC='_timest.gif' WIDTH=14 HEIGHT=19 ALT=' tX' TITLE='tX'> ";
  althtmldef "tX" as " &times;<SUB>t</SUB> ";
  latexdef "tX" as "\times_t";
htmldef "^ko" as
    " <IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' TITLE='^'>" +
    "<IMG SRC='subk.gif' WIDTH=7 HEIGHT=19 ALT=' k' TITLE='k'>" +
    "<IMG SRC='subo.gif' WIDTH=6 HEIGHT=19 ALT=' o' TITLE='o'> ";
  althtmldef "^ko" as " ^<SUB><I>ko</I></SUB> ";
  latexdef "^ko" as "\uparrow_{ko}";
htmldef "KQ" as "KQ"; althtmldef "KQ" as "KQ";
  latexdef "KQ" as "{\rm KQ}";
htmldef "Homeo" as
    " <IMG SRC='_homeo.gif' WIDTH=43 HEIGHT=19 ALT=' Homeo' TITLE='Homeo'> ";
  althtmldef "Homeo" as " Homeo ";
  latexdef "Homeo" as "{\rm Homeo}";
htmldef "~=" as
    " <IMG SRC='simeq.gif' WIDTH=13 HEIGHT=19 ALT=' ~=' TITLE='~='> ";
  althtmldef "~=" as " &#8771; ";
  latexdef "~=" as "\simeq";
htmldef "fBas" as
    "<IMG SRC='_fbas.gif' WIDTH=29 HEIGHT=19 ALT=' fBas' TITLE='fBas'>";
  althtmldef "fBas" as "fBas";
  latexdef "fBas" as "{\rm fBas}";
htmldef "filGen" as
    "<IMG SRC='_filgen.gif' WIDTH=40 HEIGHT=19 ALT=' filGen' TITLE='filGen'>";
  althtmldef "filGen" as "filGen";
  latexdef "filGen" as "{\rm filGen}";
htmldef "Fil" as
    "<IMG SRC='_fil.gif' WIDTH=17 HEIGHT=19 ALT=' Fil' TITLE='Fil'>";
  althtmldef "Fil" as "Fil";
  latexdef "Fil" as "{\rm Fil}";
htmldef "UFil" as
    "<IMG SRC='_ufil.gif' WIDTH=27 HEIGHT=19 ALT=' UFil' TITLE='UFil'>";
  althtmldef "UFil" as "UFil";
  latexdef "UFil" as "{\rm UFil}";
htmldef "UFL" as "UFL";
  althtmldef "UFL" as "UFL";
  latexdef "UFL" as "{\rm UFL}";
htmldef "FilMap" as
   " <IMG SRC='_filmap.gif' WIDTH=45 HEIGHT=19 ALT=' FilMap' TITLE='FilMap'> ";
  althtmldef "FilMap" as " FilMap ";
  latexdef "FilMap" as "{\rm FilMap}";
htmldef "fLimf" as
    " <IMG SRC='_flimf.gif' WIDTH=37 HEIGHT=19 ALT=' fLimf' TITLE='fLimf'> ";
  althtmldef "fLimf" as " fLimf ";
  latexdef "fLimf" as "{\rm fLimf}";
htmldef "fLim" as
    " <IMG SRC='_flim.gif' WIDTH=31 HEIGHT=19 ALT=' fLim' TITLE='fLim'> ";
  althtmldef "fLim" as " fLim ";
  latexdef "fLim" as "{\rm fLim}";
htmldef "fClus" as
    " <IMG SRC='_fclus.gif' WIDTH=34 HEIGHT=19 ALT=' fClus' TITLE='fClus'> ";
  althtmldef "fClus" as " fClus ";
  latexdef "fClus" as "{\rm fClus}";
htmldef "fClusf" as
   " <IMG SRC='_fclusf.gif' WIDTH=40 HEIGHT=19 ALT=' fClusf' TITLE='fClusf'> ";
  althtmldef "fClusf" as " fClusf ";
  latexdef "fClusf" as "{\rm fClusf}";
htmldef "TopMnd" as "TopMnd"; althtmldef "TopMnd" as "TopMnd";
  latexdef "TopMnd" as "{\rm TopMnd}";
htmldef "TopGrp" as
    "<IMG SRC='_topgrp.gif' WIDTH=48 HEIGHT=19 ALT=' TopGrp' TITLE='TopGrp'>";
  althtmldef "TopGrp" as "TopGrp";
  latexdef "TopGrp" as "{\rm TopGrp}";
htmldef "tsums" as " tsums ";
  althtmldef "tsums" as " tsums ";
  latexdef "tsums" as "{\rm tsums}";
htmldef "TopRing" as
    "<IMG SRC='_topring.gif' WIDTH=53 HEIGHT=19 " +
    "ALT=' TopRing' TITLE='TopRing'>";
  althtmldef "TopRing" as "TopRing";
  latexdef "TopRing" as "{\rm TopRing}";
htmldef "TopDRing" as "TopDRing"; althtmldef "TopDRing" as "TopDRing";
  latexdef "TopDRing" as "{\rm TopDRing}";
htmldef "TopMod" as "TopMod"; althtmldef "TopMod" as "TopMod";
  latexdef "TopMod" as "{\rm TopMod}";
htmldef "TopVec" as
    "<IMG SRC='_topvec.gif' WIDTH=43 HEIGHT=19 ALT=' TopVec' TITLE='TopVec'>";
  althtmldef "TopVec" as "TopVec";
  latexdef "TopVec" as "{\rm TopVec}";
htmldef "*MetSp" as
    "<IMG SRC='infty.gif' WIDTH=17 HEIGHT=19 ALT=' *' TITLE='*'>" +
    "<IMG SRC='_metsp.gif' WIDTH=41 HEIGHT=19 ALT=' MetSp' TITLE='MetSp'>";
  althtmldef "*MetSp" as "&infin;MetSp";
  latexdef "*MetSp" as "\infty{\rm MetSp}";
htmldef "MetSp" as
    "<IMG SRC='_metsp.gif' WIDTH=41 HEIGHT=19 ALT=' MetSp' TITLE='MetSp'>";
  althtmldef "MetSp" as "MetSp";
  latexdef "MetSp" as "{\rm MetSp}";
htmldef "toMetSp" as "toMetSp"; althtmldef "toMetSp" as "toMetSp";
  latexdef "toMetSp" as "{\rm toMetSp}";
htmldef "norm" as "<IMG SRC='_norm.gif' WIDTH=32 HEIGHT=19 ALT=' norm' " +
    "TITLE='norm'>";
  althtmldef "norm" as 'norm';
  latexdef "norm" as '{\rm norm}';
htmldef "NrmGrp" as "NrmGrp"; althtmldef "NrmGrp" as "NrmGrp";
  latexdef "NrmGrp" as "{\rm NrmGrp}";
htmldef "toNrmGrp" as " toNrmGrp "; althtmldef "toNrmGrp" as " toNrmGrp ";
  latexdef "toNrmGrp" as " {\rm toNrmGrp} ";
htmldef "NrmRing" as "NrmRing"; althtmldef "NrmRing" as "NrmRing";
  latexdef "NrmRing" as "{\rm NrmRing}";
htmldef "NrmMod" as "NrmMod"; althtmldef "NrmMod" as "NrmMod";
  latexdef "NrmMod" as "{\rm NrmMod}";
htmldef "NrmVec" as "NrmVec"; althtmldef "NrmVec" as "NrmVec";
  latexdef "NrmVec" as "{\rm NrmVec}";
htmldef "normOp" as
    "<IMG SRC='_normop.gif' WIDTH=52 HEIGHT=19 ALT=' normOp' TITLE='normOp'>";
  althtmldef "normOp" as " normOp ";
  latexdef "normOp" as "{\rm normOp}";
htmldef "NGHom" as " NGHom ";
  althtmldef "NGHom" as " NGHom ";
  latexdef "NGHom" as "{\rm NGHom}";
htmldef "NMHom" as " NMHom ";
  althtmldef "NMHom" as " NMHom ";
  latexdef "NMHom" as "{\rm NMHom}";
htmldef "II" as "<IMG SRC='bbi.gif' WIDTH=7 HEIGHT=19 ALT=' II' TITLE='II'>";
  althtmldef "II" as "II";
  latexdef "II" as "{\rm II}";
htmldef "-cn->" as "<IMG SRC='_cnmap.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' -cn-&gt;' TITLE='-cn-&gt;'>";
  althtmldef "-cn->" as '&ndash;<FONT SIZE=-1 FACE=sans-serif>cn</FONT>&rarr;';
  latexdef "-cn->" as
    "\raisebox{.5ex}{${\textstyle{\:}_{\mbox{\footnotesize\rm cn" +
    "}}}\atop{\textstyle{" +
    "\longrightarrow}\atop{\textstyle{}^{\mbox{\footnotesize\rm {\ }}}}}$}";
htmldef "Htpy" as " Htpy ";
  althtmldef "Htpy" as " Htpy ";
  latexdef "Htpy" as "{\rm Htpy}";
htmldef "PHtpy" as
    "<IMG SRC='_phtpy.gif' WIDTH=41 HEIGHT=19 ALT=' PHtpy' TITLE='PHtpy'>";
  althtmldef "PHtpy" as "PHtpy";
  latexdef "PHtpy" as "{\rm PHtpy}";
htmldef "~=ph" as
    " <IMG SRC='_simeqph.gif' WIDTH=26 HEIGHT=19 ALT=' ~=ph' TITLE='~=ph'> ";
  althtmldef "~=ph" as " &#8771;<SUB><I>ph</I></SUB>";
  latexdef "~=ph" as "\simeq_{ph}";
/*
htmldef "pi1b" as
    "<IMG SRC='pi.gif' WIDTH=10 HEIGHT=19 ALT=' pi' TITLE='pi'>" +
    "<IMG SRC='sub1.gif' WIDTH=4 HEIGHT=19 ALT=' 1' TITLE='1'>" +
    "<IMG SRC='subb.gif' WIDTH=6 HEIGHT=19 ALT=' b' TITLE='b'>";
  althtmldef "pi1b" as "<I>&pi;<SUB>1b</SUB></I>";
  latexdef "pi1b" as "\pi_{1b}";
*/
htmldef "*p" as
    "<IMG SRC='_astp.gif' WIDTH=14 HEIGHT=19 ALT=' *p' TITLE='*p'>";
  althtmldef "*p" as "*<SUB>&#x1D45D;</SUB>";
  latexdef "*p" as "*_p";
htmldef "Om1" as
    " <IMG SRC='comega.gif' WIDTH=11 HEIGHT=19 ALT=' Om' TITLE='Om'>" +
    "<IMG SRC='sub1.gif' WIDTH=4 HEIGHT=19 ALT=' 1' TITLE='1'> ";
  althtmldef "Om1" as " &Omega;<SUB>1</SUB> ";
  latexdef "Om1" as "\Omega_1";
htmldef "OmN" as
    " <IMG SRC='comega.gif' WIDTH=11 HEIGHT=19 ALT=' Om' TITLE='Om'>" +
    "<IMG SRC='subn.gif' WIDTH=6 HEIGHT=19 ALT=' N' TITLE='N'> ";
  althtmldef "OmN" as " &Omega;<SUB>&#x1D45B;</SUB> ";
  latexdef "OmN" as "\Omega_n";
htmldef "pi1" as
    " <IMG SRC='pi.gif' WIDTH=10 HEIGHT=19 ALT=' pi' TITLE='pi'>" +
    "<IMG SRC='sub1.gif' WIDTH=4 HEIGHT=19 ALT=' 1' TITLE='1'> ";
  althtmldef "pi1" as " <I>&pi;</I><SUB>1</SUB> ";
  latexdef "pi1" as "\pi_1";
htmldef "piN" as
    " <IMG SRC='pi.gif' WIDTH=10 HEIGHT=19 ALT=' pi' TITLE='pi'>" +
    "<IMG SRC='subn.gif' WIDTH=6 HEIGHT=19 ALT=' N' TITLE='N'> ";
  althtmldef "piN" as " <I>&pi;<SUB>n</SUB></I> ";
  latexdef "piN" as "\pi_n";
/*
htmldef "~~>m" as "<IMG SRC='_squigm.gif' WIDTH=25 HEIGHT=19 " +
    "ALT=' ~~&gt;m' TITLE='~~&gt;m'>";
  althtmldef "~~>m" as '<FONT FACE=sans-serif>&#8669;<SUB>m</SUB></FONT>';
  latexdef "~~>m" as "\rightsquigarrow_{\rm m}";
*/
htmldef "CMod" as "CMod"; althtmldef "CMod" as "CMod";
  latexdef "CMod" as "{\rm CMod}";
htmldef "CPreHil" as
  "<IMG SRC='_cprehil.gif' WIDTH=50 HEIGHT=19 ALT=' CPreHil' TITLE='CPreHil'>";
  althtmldef "CPreHil" as "CPreHil";
  latexdef "CPreHil" as "{\rm CPreHil}";
htmldef "toCHil" as "toCHil"; althtmldef "toCHil" as "toCHil";
  latexdef "toCHil" as "{\rm toCHil}";
htmldef "CauFil" as "CauFil"; althtmldef "CauFil" as "CauFil";
  latexdef "CauFil" as "{\rm CauFil}";
htmldef "Cau" as
    "<IMG SRC='_cau.gif' WIDTH=26 HEIGHT=19 ALT=' Cau' TITLE='Cau'>";
  althtmldef "Cau" as "Cau";
  latexdef "Cau" as "{\rm Cau}";
htmldef "CMet" as
    "<IMG SRC='_cmet.gif' WIDTH=35 HEIGHT=19 ALT=' CMet' TITLE='CMet'>";
  althtmldef "CMet" as "CMet";
  latexdef "CMet" as "{\rm CMet}";
htmldef "CMetSp" as "CMetSp"; althtmldef "CMetSp" as "CMetSp";
  latexdef "CMetSp" as "{\rm CMetSp}";
htmldef "Ban" as "Ban"; althtmldef "Ban" as "Ban";
  latexdef "Ban" as "{\rm Ban}";
htmldef "CHil" as
    "<IMG SRC='_chil.gif' WIDTH=28 HEIGHT=19 ALT=' CHil' TITLE='CHil'>";
  althtmldef "CHil" as "CHil";
  latexdef "CHil" as "{\rm CHil}";
htmldef "vol*" as
    "<IMG SRC='_vol.gif' WIDTH=19 HEIGHT=19 ALT=' vol' TITLE='vol'>" +
    "<IMG SRC='supast.gif' WIDTH=6 HEIGHT=19 ALT=' *' TITLE='*'>";
  althtmldef "vol*" as "vol*";
  latexdef "vol*" as "{\rm vol*}";
htmldef "vol" as
    "<IMG SRC='_vol.gif' WIDTH=19 HEIGHT=19 ALT=' vol' TITLE='vol'>";
  althtmldef "vol" as "vol";
  latexdef "vol" as "{\rm vol}";
htmldef "MblFn" as "MblFn";
  althtmldef "MblFn" as "MblFn"; latexdef "MblFn" as "{\rm MblFn}";
htmldef "L^1" as
    "<IMG SRC='cl.gif' WIDTH=10 HEIGHT=19 ALT=' L' TITLE='L'>" +
    "<IMG SRC='sup1.gif' WIDTH=4 HEIGHT=19 ALT=' ^1' TITLE='^1'>";
  althtmldef "L^1" as "&#x1D43F;<SUP>1</SUP>";
  latexdef "L^1" as "L^1";
htmldef "S.1" as
    "<IMG SRC='_int1.gif' WIDTH=11 HEIGHT=19 ALT=' S.1' TITLE='S.1'>";
  althtmldef "S.1" as "&int;<SUB>1</SUB>";
  latexdef "S.1" as "\int_2";
htmldef "S.2" as
    "<IMG SRC='_int2.gif' WIDTH=13 HEIGHT=19 ALT=' S.2' TITLE='S.2'>";
  althtmldef "S.2" as "&int;<SUB>2</SUB>";
  latexdef "S.2" as "\int_2";
htmldef "S." as "<IMG SRC='int.gif' WIDTH=10 HEIGHT=19 ALT=' S.' TITLE='S.'>";
  althtmldef "S." as "&int;";
  latexdef "S." as "\int";
htmldef "S_" as "<IMG SRC='int.gif' WIDTH=10 HEIGHT=19 ALT=' S_' TITLE='S_'>_";
  althtmldef "S_" as "&#x2A1C;";
  latexdef "S_" as "\int";
htmldef "_d" as " <IMG SRC='rmd.gif' WIDTH=8 HEIGHT=19 ALT=' _d' TITLE='_d'>";
  althtmldef "_d" as " d";
  latexdef "_d" as "\,{\rm d}";
htmldef "0p" as "<IMG SRC='0.gif' WIDTH=8 HEIGHT=19 ALT=' 0' TITLE='0'>" +
    "<IMG SRC='subp.gif' WIDTH=7 HEIGHT=19 ALT=' p' TITLE='p'>";
  althtmldef "0p" as "0<SUB>&#x1D45D;</SUB>";
  latexdef "0p" as "0_p";
htmldef "_D" as
    " <IMG SRC='rmcd.gif' WIDTH=10 HEIGHT=19 ALT=' _D' TITLE='_D'> ";
  althtmldef "_D" as " D ";
  latexdef "_D" as "{\rm D}";
htmldef "limCC" as
    " lim<IMG SRC='bbc.gif' WIDTH=12 HEIGHT=19 ALT=' CC' TITLE='CC'> ";
  althtmldef "limCC" as " lim<sub>&#8450;</sub> ";
  latexdef "limCC" as "{\rm lim}_\mathbb{C}";
htmldef "Dn" as
    " <IMG SRC='rmcd.gif' WIDTH=10 HEIGHT=19 ALT=' D' TITLE='D'>" +
    "<IMG SRC='supn.gif' WIDTH=6 HEIGHT=19 ALT=' n' TITLE='n'>";
  althtmldef "Dn" as "D<SUP>&#x1D45B;</SUP>";
  latexdef "Dn" as "{\rm D}^n";
htmldef "C^n" as "<IMG SRC='cc.gif' WIDTH=12 HEIGHT=19 ALT=' C' TITLE='C'>" +
    "<IMG SRC='supn.gif' WIDTH=6 HEIGHT=19 ALT=' ^n' TITLE='^n'>";
  althtmldef "C^n" as "<I>C<SUP>n</SUP></I>";
  latexdef "C^n" as "C^n";
htmldef "Monic1p" as "Monic<sub>1p</sub>";
  althtmldef "Monic1p" as "Monic<sub>1p</sub>";
  latexdef "Monic1p" as "{\rm Monic}_{1p}";
htmldef "Unic1p" as "Unic<sub>1p</sub>";
  althtmldef "Unic1p" as "Unic<sub>1p</sub>";
  latexdef "Unic1p" as "{\rm Unic}_{1p}";
htmldef "quot1p" as "quot<sub>1p</sub>";
  althtmldef "quot1p" as "quot<sub>1p</sub>";
  latexdef "quot1p" as "{\rm quot}_{1p}";
htmldef "rem1p" as "rem<sub>1p</sub>";
  althtmldef "rem1p" as "rem<sub>1p</sub>";
  latexdef "rem1p" as "{\rm rem}_{1p}";
htmldef "idlGen1p" as "idlGen<sub>1p</sub>";
  althtmldef "idlGen1p" as "idlGen<sub>1p</sub>";
  latexdef "idlGen1p" as "{\rm idlGen}_{1p}";
htmldef "Poly" as "Poly";
  althtmldef "Poly" as "Poly";
  latexdef "Poly" as "\rm{Poly}";
htmldef "Xp" as "<IMG SRC='cx.gif' WIDTH=13 HEIGHT=19 ALT=' X' TITLE='X'>" +
    "<IMG SRC='subp.gif' WIDTH=7 HEIGHT=19 ALT=' p' TITLE='p'>";
  althtmldef "Xp" as "<I>X<SUB>p</SUB></I>";
  latexdef "Xp" as "X_p";
htmldef "coeff" as "coeff";
  althtmldef "coeff" as "coeff";
  latexdef "coeff" as "\rm{coeff}";
htmldef "deg" as "deg";
  althtmldef "deg" as "deg";
  latexdef "deg" as "\rm{deg}";
htmldef "quot" as " quot ";
  althtmldef "quot" as " quot ";
  latexdef "quot" as "\rm{quot}";
htmldef "AA" as "<IMG SRC='bba.gif' WIDTH=13 HEIGHT=19 ALT=' AA' TITLE='AA'>";
  althtmldef "AA" as '&#120120;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "AA" as "\mathbb{A}";
htmldef "Tayl" as " Tayl ";
  althtmldef "Tayl" as " Tayl ";
  latexdef "Tayl" as "\rm{Tayl}";
htmldef "Ana" as "Ana";
  althtmldef "Ana" as "Ana";
  latexdef "Ana" as "\rm{Ana}";
htmldef "~~>u" as "<IMG SRC='rightsquigarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' ~~&gt;' TITLE='~~&gt;'>" +
    "<IMG SRC='subu.gif' WIDTH=6 HEIGHT=19 ALT=' u' TITLE='u'>";
  althtmldef "~~>u" as
    "&#8669;<SUB>&#x1D462;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~~>u" as "\rightsquigarrow_u";
htmldef "log" as
    "<IMG SRC='_log.gif' WIDTH=20 HEIGHT=19 ALT=' log' TITLE='log'>";
  althtmldef "log" as "log";
  latexdef "log" as "\log";
htmldef "^c" as
    " <IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' TITLE='^'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'> ";
  althtmldef "^c" as "&uarr;<SUB>&#x1D450;</SUB>";
  latexdef "^c" as "\uparrow_c";
htmldef "arcsin" as "arcsin";
  althtmldef "arcsin" as "arcsin";
  latexdef "arcsin" as "\arcsin";
htmldef "arccos" as "arccos";
  althtmldef "arccos" as "arccos";
  latexdef "arccos" as "\arccos";
htmldef "arctan" as "arctan";
  althtmldef "arctan" as "arctan";
  latexdef "arctan" as "\arctan";
htmldef "area" as "area";
  althtmldef "area" as "area";
  latexdef "area" as "{\rm area}";
htmldef "gamma" as
    "<IMG SRC='gamma.gif' WIDTH=11 HEIGHT=19 ALT=' gamma' TITLE='gamma'>";
  althtmldef "gamma" as "&gamma;";
  latexdef "gamma" as "\gamma";
htmldef "theta" as
    "<IMG SRC='theta.gif' WIDTH=8 HEIGHT=19 ALT=' theta' TITLE='theta'>";
  althtmldef "theta" as "&theta;";
  latexdef "theta" as "\theta";
htmldef "Lam" as "&Lambda;";
  althtmldef "Lam" as "&Lambda;";
  latexdef "Lam" as "\Lambda";
htmldef "psi" as "&psi;";
  althtmldef "psi" as "&psi;";
  latexdef "psi" as "\psi";
htmldef "ppi" as "<U>&pi;</U>";
  althtmldef "ppi" as "<U>&pi;</U>";
  latexdef "ppi" as "\pi";
htmldef "mmu" as
    "<IMG SRC='mu.gif' WIDTH=10 HEIGHT=19 ALT=' mmu' TITLE='mmu'>";
  althtmldef "mmu" as "&mu;";
  latexdef "mmu" as "\mu";
htmldef "sigma" as
    " <IMG SRC='sigma.gif' WIDTH=10 HEIGHT=19 ALT=' sigma' TITLE='sigma'> ";
  althtmldef "sigma" as " &sigma; ";
  latexdef "sigma" as " \sigma ";
htmldef "DChr" as "DChr";
  althtmldef "DChr" as "DChr";
  latexdef "DChr" as "{\rm DChr}";
htmldef "/L" as
    " <IMG SRC='solidus.gif' WIDTH=6 HEIGHT=19 ALT=' /' TITLE='/'>" +
    "<IMG SRC='subcl.gif' WIDTH=8 HEIGHT=19 ALT=' L' TITLE='L'>";
  althtmldef "/L" as " /<sub><i>L</i></sub> ";
  latexdef "/L" as " /_L ";

/* Graph theory */
htmldef "UHGrph" as ' UHGrph ';
 althtmldef "UHGrph" as ' UHGrph ';
 latexdef "UHGrph" as "{\rm UHGrph}";
htmldef "UMGrph" as " UMGrph "; althtmldef "UMGrph" as " UMGrph ";
  latexdef "UMGrph" as " {\rm UMGrph} ";
htmldef "USLGrph" as ' USLGrph ';
 althtmldef "USLGrph" as ' USLGrph ';
 latexdef "USLGrph" as "{\rm USLGrph}";
htmldef "USGrph" as " USGrph ";
 althtmldef "USGrph" as " USGrph ";
 latexdef "USGrph" as " {\rm USGrph} ";
htmldef "Neighbors" as ' Neighbors ';
 althtmldef "Neighbors" as ' Neighbors ';
 latexdef "Neighbors" as "{\rm Neighbors}";
htmldef "ComplUSGrph" as ' ComplUSGrph ';
 althtmldef "ComplUSGrph" as ' ComplUSGrph ';
 latexdef "ComplUSGrph" as "{\rm ComplUSGrph}";
htmldef "UnivVertex" as ' UnivVertex ';
 althtmldef "UnivVertex" as ' UnivVertex ';
 latexdef "UnivVertex" as "{\rm UnivVertex}";
htmldef "VDeg" as " VDeg "; althtmldef "VDeg" as " VDeg ";
  latexdef "VDeg" as " {\rm VDeg} ";
htmldef "Walks" as " Walks "; althtmldef "Walks" as " Walks ";
  latexdef "Walks" as " {\rm Walks} ";
htmldef "Trails" as " Trails "; althtmldef "Trails" as " Trails ";
  latexdef "Trails" as " {\rm Trails} ";
htmldef "Paths" as " Paths "; althtmldef "Paths" as " Paths ";
  latexdef "Paths" as " {\rm Paths} ";
htmldef "SPaths" as " SPaths "; althtmldef "SPaths" as " SPaths ";
  latexdef "SPaths" as " {\rm SPaths} ";
htmldef "WalkOn" as " WalkOn "; althtmldef "WalkOn" as " WalkOn ";
  latexdef "WalkOn" as " {\rm WalkOn} ";
htmldef "TrailOn" as " TrailOn "; althtmldef "TrailOn" as " TrailOn ";
  latexdef "TrailOn" as " {\rm TrailOn} ";
htmldef "PathOn" as " PathOn "; althtmldef "PathOn" as " PathOn ";
  latexdef "PathOn" as " {\rm PathOn} ";
htmldef "SPathOn" as ' SPathOn ';
 althtmldef "SPathOn" as ' SPathOn ';
 latexdef "SPathOn" as "{\rm SPathOn}";
htmldef "Circuits" as " Circuits "; althtmldef "Circuits" as " Circuits ";
  latexdef "Circuits" as " {\rm Circuits} ";
htmldef "Cycles" as " Cycles "; althtmldef "Cycles" as " Cycles ";
  latexdef "Cycles" as " {\rm Cycles} ";
htmldef "ConnGrph" as ' ConnGrph ';
 althtmldef "ConnGrph" as ' ConnGrph ';
 latexdef "ConnGrph" as "{\rm ConnGrph}";

htmldef "Plig" as
    "<IMG SRC='_plig.gif' WIDTH=25 HEIGHT=19 ALT=' Plig' TITLE='Plig'>";
  althtmldef "Plig" as "Plig";
  latexdef "Plig" as "{\rm Plig}";
htmldef "RPrime" as "RPrime"; althtmldef "RPrime" as "RPrime";
  latexdef "RPrime" as "{\rm RPrime}";
/*
htmldef "UFD" as "UFD"; althtmldef "UFD" as "UFD";
  latexdef "UFD" as "{\rm UFD}";
*/
htmldef "t+" as "<IMG SRC='t.gif' WIDTH=7 HEIGHT=19 ALT=' t' TITLE='t'>" +
    "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>";
  althtmldef "t+" as "t+";
  latexdef "t+" as "{\rm t}+";
htmldef "t*" as "<IMG SRC='t.gif' WIDTH=7 HEIGHT=19 ALT=' t' TITLE='t'>" +
    "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT=' *' TITLE='*'>";
  althtmldef "t*" as "t*";
  latexdef "t*" as "{\rm t}*";
htmldef "GrpOp" as
    "<IMG SRC='_grpop.gif' WIDTH=44 HEIGHT=19 ALT=' GrpOp' TITLE='GrpOp'>";
  althtmldef "GrpOp" as "GrpOp";
  latexdef "GrpOp" as "{\rm GrpOp}";
htmldef "GId" as "GId";
  althtmldef "GId" as "GId";
  latexdef "GId" as "{\rm GId}";
htmldef "inv" as
    "<IMG SRC='_inv.gif' WIDTH=19 HEIGHT=19 ALT=' inv' TITLE='inv'>";
  althtmldef "inv" as "inv";
  latexdef "inv" as "{\rm inv}";
htmldef "/g" as " <IMG SRC='_divg.gif' WIDTH=11 HEIGHT=19 ALT=' /g' " +
    "TITLE='/g'> ";
  althtmldef "/g" as " /<SUB>&#x1D454;</SUB> ";
  latexdef "/g" as "/_g";
htmldef "^g" as
    "<IMG SRC='_hatg.gif' WIDTH=11 HEIGHT=19 ALT=' ^g' TITLE='^g'>";
  althtmldef "^g" as "&uarr;<SUB>&#x1D454;</SUB>";
  latexdef "^g" as "\uparrow_g";
htmldef "AbelOp" as
    "<IMG SRC='_abelop.gif' WIDTH=47 HEIGHT=19 ALT=' AbelOp' TITLE='AbelOp'>";
  althtmldef "AbelOp" as "AbelOp";
  latexdef "AbelOp" as "{\rm AbelOp}";
htmldef "SubGrpOp" as
    "<IMG SRC='_subgrpop.gif' WIDTH=68 HEIGHT=19 " +
    "ALT=' SubGrpOp' TITLE='SubGrpOp'>";
  althtmldef "SubGrpOp" as "SubGrpOp";
  latexdef "SubGrpOp" as "{\rm SubGrpOp}";
htmldef "Ass" as
    "<IMG SRC='_ass.gif' WIDTH=22 HEIGHT=19 ALT=' Ass' TITLE='Ass'>";
  althtmldef "Ass" as "Ass";
  latexdef "Ass" as "{\rm Ass}";
htmldef "ExId" as
    " <IMG SRC='_exid.gif' WIDTH=29 HEIGHT=19 ALT=' ExId' TITLE='ExId'> ";
  althtmldef "ExId" as " ExId ";
  latexdef "ExId" as "{\rm ExId}";
htmldef "Magma" as
    "<IMG SRC='_magma.gif' WIDTH=48 HEIGHT=19 ALT=' Magma' TITLE='Magma'>";
  althtmldef "Magma" as "Magma";
  latexdef "Magma" as "{\rm Magma}";
htmldef "SemiGrp" as
  "<IMG SRC='_semigrp.gif' WIDTH=56 HEIGHT=19 ALT=' SemiGrp' TITLE='SemiGrp'>";
  althtmldef "SemiGrp" as "SemiGrp";
  latexdef "SemiGrp" as "{\rm SemiGrp}";
htmldef "MndOp" as "MndOp";
  althtmldef "MndOp" as "MndOp";
  latexdef "MndOp" as "{\rm MndOp}";
htmldef "GrpOpHom" as " GrpOpHom ";
  althtmldef "GrpOpHom" as " GrpOpHom ";
  latexdef "GrpOpHom" as "{\rm GrpOpHom}";
htmldef "GrpOpIso" as
    " <IMG SRC='_grpiso.gif' WIDTH=42 HEIGHT=19 " +
    "ALT=' GrpOpIso' TITLE='GrpOpIso'> ";
  althtmldef "GrpOpIso" as " GrpOpIso ";
  latexdef "GrpOpIso" as "{\rm GrpOpIso}";
htmldef "RingOps" as
  "<IMG SRC='_ringops.gif' WIDTH=55 HEIGHT=19 ALT=' RingOps' TITLE='RingOps'>";
  althtmldef "RingOps" as "RingOps";
  latexdef "RingOps" as "{\rm RingOps}";
htmldef "DivRingOps" as "<IMG SRC='_divringops.gif' WIDTH=77 HEIGHT=19" +
      " ALT=' DivRingOps' TITLE='DivRingOps'>";
  althtmldef "DivRingOps" as "DivRingOps";
  latexdef "DivRingOps" as "{\rm DivRingOps}";
htmldef "*-Fld" as
    "<IMG SRC='_astfld.gif' WIDTH=32 HEIGHT=19 ALT=' *-Fld' TITLE='*-Fld'>";
  althtmldef "*-Fld" as "*-Fld";
  latexdef "*-Fld" as "\ast-{\rm Fld}";
htmldef "Com2" as
    "<IMG SRC='_com2.gif' WIDTH=35 HEIGHT=19 ALT=' Com2' TITLE='Com2'>";
  althtmldef "Com2" as "Com2";
  latexdef "Com2" as "{\rm Com2}";
htmldef "Fld" as
    "<IMG SRC='_fld.gif' WIDTH=21 HEIGHT=19 ALT=' Fld' TITLE='Fld'>";
  althtmldef "Fld" as "Fld";
  latexdef "Fld" as "{\rm Fld}";
htmldef "CVecOLD" as
    "<IMG SRC='_cvec.gif' WIDTH=34 HEIGHT=19 ALT=' CVec' TITLE='CVec'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "CVecOLD" as "CVec<SUB>OLD</SUB>";
  latexdef "CVecOLD" as "{\rm CVec_{OLD}}";
htmldef "NrmCVec" as
  "<IMG SRC='_nrmcvec.gif' WIDTH=62 HEIGHT=19 ALT=' NrmCVec' TITLE='NrmCVec'>";
  althtmldef "NrmCVec" as "NrmCVec";
  latexdef "NrmCVec" as "{\rm NrmCVec}";
htmldef "+v" as "<IMG SRC='_plv.gif' WIDTH=19 HEIGHT=19 ALT=' +v' TITLE='+v'>";
  althtmldef "+v" as ' +<SUB>&#x1D463;</SUB> ';
  latexdef "+v" as '+_v';
htmldef "BaseSet" as
  "<IMG SRC='_baseset.gif' WIDTH=51 HEIGHT=19 ALT=' BaseSet' TITLE='BaseSet'>";
  althtmldef "BaseSet" as "BaseSet";
  latexdef "BaseSet" as "{\rm BaseSet}";
htmldef ".sOLD" as
    "<IMG SRC='_cds.gif' WIDTH=9 HEIGHT=19 ALT=' .s' TITLE='.s'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef ".sOLD" as ' <B>&middot;</B><SUB>&#x1D460;OLD</SUB> ';
  latexdef ".sOLD" as '\cdot_{s{\rm OLD}}';
htmldef "0vec" as
    "<IMG SRC='_0vec.gif' WIDTH=25 HEIGHT=19 ALT=' 0vec' TITLE='0vec'>";
  althtmldef "0vec" as '0<SUB>vec</SUB>';
  latexdef "0vec" as '0_{\rm vec}';
htmldef "-v" as "<IMG SRC='_mv.gif' WIDTH=17 HEIGHT=19 ALT=' -v' TITLE='-v'>";
  althtmldef "-v" as ' &minus;<SUB>&#x1D463;</SUB> ';
  latexdef "-v" as '-_v';
htmldef "normCV" as "<IMG SRC='_norm.gif' WIDTH=32 HEIGHT=19 ALT=' norm' " +
    "TITLE='norm'><SUB>CV</SUB>";
  althtmldef "normCV" as 'norm<SUB>CV</SUB>';
  latexdef "normCV" as '{\rm norm_{CV}}';
    /* 24-Apr-2007 nm These need images. */
htmldef "IndMet" as
    "<IMG SRC='_indmet.gif' WIDTH=45 HEIGHT=19 ALT=' IndMet' TITLE='IndMet'>";
  althtmldef "IndMet" as "IndMet";
  latexdef "IndMet" as "{\rm IndMet}";
htmldef ".iOLD" as
    "<IMG SRC='_cdi.gif' WIDTH=7 HEIGHT=19 ALT=' .i' TITLE='.i'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef ".iOLD" as '<B>&middot;</B><SUB>&#x1D456;OLD</SUB>';
  latexdef ".iOLD" as '\cdot_{i{\rm OLD}}';
htmldef "SubSp" as
    "<IMG SRC='_subsp.gif' WIDTH=40 HEIGHT=19 ALT=' SubSp' TITLE='SubSp'>";
  althtmldef "SubSp" as "SubSp";
  latexdef "SubSp" as "{\rm SubSp}";
htmldef "LnOp" as
    " <IMG SRC='_lnop.gif' WIDTH=36 HEIGHT=19 ALT=' LnOp' TITLE='LnOp'> ";
  althtmldef "LnOp" as " LnOp ";
  latexdef "LnOp" as "{\rm LnOp}";
htmldef "normOpOLD" as
    "<IMG SRC='_normop.gif' WIDTH=52 HEIGHT=19 ALT=' normOp' TITLE='normOp'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "normOpOLD" as " normOp<SUB>OLD</SUB> ";
  latexdef "normOpOLD" as "{\rm normOp_{OLD}}";
htmldef "BLnOp" as
    " <IMG SRC='_blnop.gif' WIDTH=45 HEIGHT=19 ALT=' BLnOp' TITLE='BLnOp'> ";
  althtmldef "BLnOp" as " BLnOp ";
  latexdef "BLnOp" as "{\rm BLnOp}";
htmldef "0op" as
    " <IMG SRC='_0op.gif' WIDTH=21 HEIGHT=19 ALT=' 0op' TITLE='0op'> ";
  althtmldef "0op" as " 0<SUB>op</SUB> ";
  latexdef "0op" as "0_\mathrm{op}";
htmldef "adj" as
    "<IMG SRC='_adj.gif' WIDTH=20 HEIGHT=19 ALT=' adj' TITLE='adj'>";
  althtmldef "adj" as "adj";
  latexdef "adj" as "{\rm adj}";
htmldef "HmOp" as
    "<IMG SRC='_hmop.gif' WIDTH=41 HEIGHT=19 ALT=' HmOp' TITLE='HmOp'>";
  althtmldef "HmOp" as "HmOp";
  latexdef "HmOp" as "{\rm HmOp}";
htmldef "CPreHilOLD" as
    "<IMG SRC='_cprehil.gif' WIDTH=50 HEIGHT=19 " +
    "ALT=' CPreHil' TITLE='CPreHil'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "CPreHilOLD" as "CPreHil<SUB>OLD</SUB>";
  latexdef "CPreHilOLD" as "{\rm CPreHil_{OLD}}";
htmldef "CBan" as
    "<IMG SRC='_cban.gif' WIDTH=35 HEIGHT=19 ALT=' CBan' TITLE='CBan'>";
  althtmldef "CBan" as "CBan";
  latexdef "CBan" as "{\rm CBan}";
htmldef "CHilOLD" as
    "<IMG SRC='_chil.gif' WIDTH=28 HEIGHT=19 ALT=' CHil' TITLE='CHil'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "CHilOLD" as "CHil<SUB>OLD</SUB>";
  latexdef "CHilOLD" as "{\rm CHil_{OLD}}";
    /* Hilbert space */
htmldef "~H" as "<IMG SRC='scrh.gif' WIDTH=19 HEIGHT=19 ALT=' ~H' TITLE='~H'>";
  althtmldef "~H" as ' &#8459;';
    /* 8459 is script H; 8460 is fraktur H */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~H" as '\mathscr{H}';
htmldef "+h" as
    " <IMG SRC='_pvh.gif' WIDTH=18 HEIGHT=19 ALT=' +h' TITLE='+h'> ";
  althtmldef "+h" as ' +<SUB>&#x210E;</SUB> ';
  latexdef "+h" as '+_h';
htmldef ".h" as
    " <IMG SRC='_cdh.gif' WIDTH=9 HEIGHT=19 ALT=' .h' TITLE='.h'> ";
  althtmldef ".h" as ' <B>&middot;</B><SUB>&#x210E;</SUB> ';
  latexdef ".h" as '\cdot_h';
htmldef "0h" as "<IMG SRC='_0vh.gif' WIDTH=14 HEIGHT=19 ALT=' 0h' TITLE='0h'>";
  althtmldef "0h" as '0<SUB>&#x210E;</SUB>';
  latexdef "0h" as '0_h';
htmldef "-h" as
    " <IMG SRC='_mvh.gif' WIDTH=16 HEIGHT=19 ALT=' -h' TITLE='-h'> ";
  althtmldef "-h" as ' &minus;<SUB>&#x210E;</SUB> ';
  latexdef "-h" as '-_h';
htmldef ".ih" as " <IMG SRC='_cdih.gif' WIDTH=13 HEIGHT=19 ALT=' .ih' " +
    "TITLE='.ih'> ";
  althtmldef ".ih" as ' <B>&middot;</B><SUB><I>ih</I></SUB> ';
  latexdef ".ih" as '\cdot_{ih}';
htmldef "normh" as "<IMG SRC='_normh.gif' WIDTH=38 HEIGHT=19 ALT=' normh' " +
    "TITLE='normh'>";
  althtmldef "normh" as 'norm<SUB>&#x210E;</SUB>';
  latexdef "normh" as '{\rm norm}_h';
htmldef "Cauchy" as "<IMG SRC='_cauchy.gif' WIDTH=47 HEIGHT=19 " +
    "ALT=' Cauchy' TITLE='Cauchy'>";
  althtmldef "Cauchy" as 'Cauchy';
  latexdef "Cauchy" as '{\rm Cauchy}';
htmldef "~~>v" as " <IMG SRC='_squigv.gif' WIDTH=21 HEIGHT=19 " +
    "ALT=' ~~&gt;v' TITLE='~~&gt;v'> ";
  althtmldef "~~>v" as
    ' &#8669;<SUB>&#x1D463;</SUB> ';
    /* 24-Sep-2017 reverted sans-serif */
  latexdef "~~>v" as '\rightsquigarrow_v';
htmldef "SH" as "<IMG SRC='_sh.gif' WIDTH=24 HEIGHT=19 ALT=' SH' TITLE='SH'>";
  althtmldef "SH" as
    ' <I><B>S</B></I><SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "SH" as '\mathscr{S}_\mathscr{H}';
htmldef "CH" as
    "<IMG SRC='_scrch.gif' WIDTH=22 HEIGHT=19 ALT=' CH' TITLE='CH'>";
  althtmldef "CH" as
    ' <I><B>C</B></I><SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "CH" as '\mathscr{C}_\mathscr{H}';
htmldef "_|_" as
    "<IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT=' _|_' TITLE='_|_'>";
  althtmldef "_|_" as '&#8869;'; /* &bottom; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "_|_" as '\perp';
htmldef "+H" as
    " <IMG SRC='_plh.gif' WIDTH=24 HEIGHT=19 ALT=' +H' TITLE='+H'> ";
  althtmldef "+H" as ' +<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "+H" as '+_\mathscr{H}';
htmldef "span" as
    "<IMG SRC='_span.gif' WIDTH=31 HEIGHT=19 ALT=' span' TITLE='span'>";
  althtmldef "span" as 'span';
  latexdef "span" as '{\rm span}';
htmldef "vH" as
    " <IMG SRC='_veeh.gif' WIDTH=21 HEIGHT=19 ALT=' vH' TITLE='vH'> ";
  althtmldef "vH" as ' &or;<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "vH" as '\vee_\mathscr{H}';
htmldef "\/H" as
    " <IMG SRC='_bigveeh.gif' WIDTH=23 HEIGHT=19 ALT=' \/H' TITLE='\/H'> ";
  althtmldef "\/H" as ' <FONT SIZE="+1">&or;' +
    '</FONT><SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/H" as '\bigvee_\mathscr{H}';
htmldef "0H" as "<IMG SRC='_0h.gif' WIDTH=20 HEIGHT=19 ALT=' 0H' TITLE='0H'>";
  althtmldef "0H" as '0<SUB>&#8459;</SUB>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "0H" as '0_\mathscr{H}';
htmldef "C_H" as
    " <IMG SRC='_cch.gif' WIDTH=23 HEIGHT=19 ALT=' C_H' TITLE='C_H'> ";
  althtmldef "C_H" as
    ' &#x1D436;<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "C_H" as 'C_\mathscr{H}';
htmldef "projh" as
    "<IMG SRC='_proj.gif' WIDTH=24 HEIGHT=19 ALT=' proj' TITLE='proj'>" +
    " <IMG SRC='subh.gif' WIDTH=6 HEIGHT=19 ALT=' h' TITLE='h'>";
  althtmldef "projh" as 'proj<SUB>&#x210E;</SUB>';
  latexdef "projh" as '{\rm proj}_h';
htmldef "0hop" as
    "<IMG SRC='_0hop.gif' WIDTH=28 HEIGHT=19 ALT=' 0hop' TITLE='0hop'>";
  althtmldef "0hop" as ' 0<SUB>hop</SUB> ';
  latexdef "0hop" as "0_\mathrm{hop}";
htmldef "Iop" as
    " <IMG SRC='_iop.gif' WIDTH=18 HEIGHT=19 ALT=' Iop' TITLE='Iop'> ";
  althtmldef "Iop" as ' I<SUB>op</SUB> ';
  latexdef "Iop" as "I_\mathrm{op}";
htmldef "+op" as
    " <IMG SRC='_plop.gif' WIDTH=25 HEIGHT=19 ALT=' +op' TITLE='+op'> ";
  althtmldef "+op" as ' +<SUB>op</SUB> ';
  latexdef "+op" as '+_\mathrm{op}';
htmldef ".op" as
    " <IMG SRC='_cdop.gif' WIDTH=16 HEIGHT=19 ALT=' .op' TITLE='.op'> ";
  althtmldef ".op" as ' <B>&middot;</B><SUB>op</SUB> ';
  latexdef ".op" as '\cdot_\mathrm{op}';
htmldef "-op" as
    " <IMG SRC='_mop.gif' WIDTH=23 HEIGHT=19 ALT=' -op' TITLE='-op'> ";
  althtmldef "-op" as ' &minus;<SUB>op</SUB> ';
  latexdef "-op" as '-_\mathrm{op}';
htmldef "+fn" as
    " <IMG SRC='_plfn.gif' WIDTH=24 HEIGHT=19 ALT=' +fn' TITLE='+fn'> ";
  althtmldef "+fn" as ' +<SUB>fn</SUB> ';
  latexdef "+fn" as '+_\mathrm{fn}';
htmldef ".fn" as
    " <IMG SRC='_cdfn.gif' WIDTH=15 HEIGHT=19 ALT=' .fn' TITLE='.fn'> ";
  althtmldef ".fn" as ' <B>&middot;</B><SUB>fn</SUB> ';
  latexdef ".fn" as '\cdot_\mathrm{fn}';
htmldef "normop" as
  "<IMG SRC='_normsubop.gif' WIDTH=45 HEIGHT=19 ALT=' normop' TITLE='normop'>";
  althtmldef "normop" as 'norm<SUB>op</SUB>';
  latexdef "normop" as '{\rm norm}_{\rm op}';
htmldef "ConOp" as
    "<IMG SRC='_conop.gif' WIDTH=44 HEIGHT=19 ALT=' ConOp' TITLE='ConOp'>";
  althtmldef "ConOp" as 'ConOp';
  latexdef "ConOp" as '{\rm ConOp}';
htmldef "LinOp" as
    "<IMG SRC='_linop.gif' WIDTH=40 HEIGHT=19 ALT=' LinOp' TITLE='LinOp'>";
  althtmldef "LinOp" as 'LinOp';
  latexdef "LinOp" as '{\rm LinOp}';
htmldef "BndLinOp" as
    "<IMG SRC='_bndlinop.gif' WIDTH=65 HEIGHT=19 " +
    "ALT=' BndLinOp' TITLE='BndLinOp'>";
  althtmldef "BndLinOp" as 'BndLinOp';
  latexdef "BndLinOp" as '{\rm BndLinOp}';
htmldef "UniOp" as
    "<IMG SRC='_uniop.gif' WIDTH=41 HEIGHT=19 ALT=' UniOp' TITLE='UniOp'>";
  althtmldef "UniOp" as 'UniOp';
  latexdef "UniOp" as '{\rm UniOp}';
htmldef "HrmOp" as
    "<IMG SRC='_hrmop.gif' WIDTH=47 HEIGHT=19 ALT=' HrmOp' TITLE='HrmOp'>";
  althtmldef "HrmOp" as 'HrmOp';
  latexdef "HrmOp" as '{\rm HrmOp}';
htmldef "normfn" as
    "<IMG SRC='_normfn.gif' WIDTH=43 HEIGHT=19 ALT=' normfn' TITLE='normfn'>";
  althtmldef "normfn" as 'norm<SUB>fn</SUB>';
  latexdef "normfn" as '{\rm norm}_{\rm fn}';
htmldef "null" as
    "<IMG SRC='_null.gif' WIDTH=24 HEIGHT=19 ALT=' null' TITLE='null'>";
  althtmldef "null" as 'null';
  latexdef "null" as '{\rm null}';
htmldef "ConFn" as
    "<IMG SRC='_confn.gif' WIDTH=42 HEIGHT=19 ALT=' ConFn' TITLE='ConFn'>";
  althtmldef "ConFn" as 'ConFn';
  latexdef "ConFn" as '{\rm ConFn}';
htmldef "LinFn" as
    "<IMG SRC='_linfn.gif' WIDTH=38 HEIGHT=19 ALT=' LinFn' TITLE='LinFn'>";
  althtmldef "LinFn" as 'LinFn';
  latexdef "LinFn" as '{\rm LinFn}';
htmldef "adjh" as
    "<IMG SRC='_adjh.gif' WIDTH=26 HEIGHT=19 ALT=' adjh' TITLE='adjh'>";
  althtmldef "adjh" as 'adj<SUB>&#x210E;</SUB>';
  latexdef "adjh" as '{\rm adj}_h';
htmldef "bra" as
    "<IMG SRC='_bra.gif' WIDTH=22 HEIGHT=19 ALT=' bra' TITLE='bra'>";
  althtmldef "bra" as 'bra';
  latexdef "bra" as '{\rm bra}';
htmldef "ketbra" as
   " <IMG SRC='_ketbra.gif' WIDTH=43 HEIGHT=19 ALT=' ketbra' TITLE='ketbra'> ";
  althtmldef "ketbra" as ' ketbra ';
  latexdef "ketbra" as '{\rm ketbra}';
htmldef "<_op" as
   " <IMG SRC='_leop.gif' WIDTH=24 HEIGHT=19 ALT=' <_op' TITLE='<_op'> ";
  althtmldef "<_op" as " &le;<SUB>op</SUB> ";
  latexdef "<_op" as '\le_{\rm op}';
htmldef "eigvec" as
    "<IMG SRC='_eigvec.gif' WIDTH=41 HEIGHT=19 ALT=' eigvec' TITLE='eigvec'>";
  althtmldef "eigvec" as 'eigvec';
  latexdef "eigvec" as '{\rm eigvec}';
htmldef "eigval" as
    "<IMG SRC='_eigval.gif' WIDTH=39 HEIGHT=19 ALT=' eigval' TITLE='eigval'>";
  althtmldef "eigval" as 'eigval';
  latexdef "eigval" as '{\rm eigval}';
htmldef "Lambda" as
    "<IMG SRC='clambda.gif' WIDTH=11 HEIGHT=19 ALT=' Lambda' TITLE='Lambda'>";
  althtmldef "Lambda" as 'Lambda';
  latexdef "Lambda" as '\Lambda';
htmldef "States" as
    "<IMG SRC='_states.gif' WIDTH=40 HEIGHT=19 ALT=' States' TITLE='States'>";
  althtmldef "States" as 'States';
  latexdef "States" as '{\rm States}';
    /* These don't have images. */
htmldef "CHStates" as
    "<IMG SRC='_chstates.gif' WIDTH=61 HEIGHT=19 " +
    "ALT=' CHStates' TITLE='CHStates'>";
  althtmldef "CHStates" as 'CHStates';
  latexdef "CHStates" as '{\rm CHStates}';
htmldef "HAtoms" as 'HAtoms';
  althtmldef "HAtoms" as 'HAtoms';
  latexdef "HAtoms" as '{\rm HAtoms}';
htmldef "<oH" as
    " <IMG SRC='_ldh.gif' WIDTH=25 HEIGHT=19 ALT=' &lt;oH' TITLE='&lt;oH'> ";
  althtmldef "<oH" as
    ' &#8918;<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "<oH" as '\lessdot_\mathscr{H}';
htmldef "MH" as
    " <IMG SRC='_mh.gif' WIDTH=27 HEIGHT=19 ALT=' MH' TITLE='MH'> ";
  althtmldef "MH" as ' &#x1D440;<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "MH" as 'M_\mathscr{H}';
htmldef "MH*" as
    " <IMG SRC='_mhast.gif' WIDTH=27 HEIGHT=19 ALT=' MH*' TITLE='MH*'> ";
  althtmldef "MH*" as ' &#x1D440;<SUB>&#8459;</SUB><SUP>*</SUP> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "MH*" as 'M_\mathscr{H}^*';

/* stuff to be sorted into the right places above: */

/* htmldef, althtmldef, latexdef for mathboxes */
/* Note the "Mathbox of" instead of "Mathbox for" to make searching easier. */

/* Mathbox of Thierry Arnoux */
htmldef "<<<" as "&lt;&lt;&lt;";
  althtmldef "<<<" as "&#x22D8;";
  latexdef "<<<" as "{\rm <<<}";
htmldef "Archi" as "Archi";
  althtmldef "Archi" as "Archi";
  latexdef "Archi" as "{\rm Archi}";
htmldef "oMnd" as "oMnd";
  althtmldef "oMnd" as "oMnd";
  latexdef "oMnd" as "{\rm oMnd}";
htmldef "oGrp" as "oGrp";
  althtmldef "oGrp" as "oGrp";
  latexdef "oGrp" as "{\rm oGrp}";
htmldef "oRing" as "oRing";
  althtmldef "oRing" as "oRing";
  latexdef "oRing" as "{\rm oRing}";
htmldef "oField" as "oField";
  althtmldef "oField" as "oField";
  latexdef "oField" as "{\rm oField}";
htmldef "SRing" as "SRing";
  althtmldef "SRing" as "SRing";
  latexdef "SRing" as "{\rm SRing}";
htmldef "SLMod" as "SLMod";
  althtmldef "SLMod" as "SLMod";
  latexdef "SLMod" as "{\rm SLMod}";
htmldef "|`v" as " &#8638;<SUB>v</SUB> ";
  althtmldef "|`v" as " &#8638;<SUB>v</SUB> ";
  latexdef "|`v" as "\restriction_v";
htmldef "RRExt" as " &#8477;Ext ";
  althtmldef "RRExt" as " &#8477;Ext ";
  latexdef "RRExt" as "\mathbb{R}{\rm Ext}";
htmldef "PsMet" as "PsMet";
  althtmldef "PsMet" as "PsMet";
  latexdef "PsMet" as "{\rm PsMet}";
htmldef "~Met" as "~Met";
  althtmldef "~Met" as "~<SUB>Met</SUB>";
  latexdef "~Met" as "~_{\rm Met}";
htmldef "pstoMet" as "pstoMet";
  althtmldef "pstoMet" as "pstoMet";
  latexdef "pstoMet" as "{\rm pstoMet}";
htmldef "HCmp" as "HCmp";
  althtmldef "HCmp" as "HCmp";
  latexdef "HCmp" as "{\rm HCmp}";
htmldef "CnExt" as "CnExt";
  althtmldef "CnExt" as "CnExt";
  latexdef "CnExt" as "{\rm CnExt}";
htmldef "UnifOn" as "UnifOn";
  althtmldef "UnifOn" as "UnifOn";
  latexdef "UnifOn" as "{\rm UnifOn}";
htmldef "UnifSt" as "UnifSt";
  althtmldef "UnifSt" as "UnifSt";
  latexdef "UnifSt" as "{\rm UnifSt}";
htmldef "UnifSp" as "UnifSp";
  althtmldef "UnifSp" as "UnifSp";
  latexdef "UnifSp" as "{\rm UnifSp}";
htmldef "toUnifSp" as "toUnifSp";
  althtmldef "toUnifSp" as "toUnifSp";
  latexdef "toUnifSp" as "{\rm toUnifSp}";
htmldef "unifTop" as "unifTop";
  althtmldef "unifTop" as "unifTop";
  latexdef "unifTop" as "{\rm unifTop}";
htmldef "uCn" as " Cn<SUB>u</SUB>";
  althtmldef "uCn" as " Cn<SUB>u</SUB>";
  latexdef "uCn" as "{\rm Cn_u}";
htmldef "CauFilU" as "CauFil<SUB>u</SUB>";
  althtmldef "CauFilU" as "CauFil<SUB>u</SUB>";
  latexdef "CauFilU" as "{\rm CauFil_u}";
htmldef "CUnifSp" as "CUnifSp";
  althtmldef "CUnifSp" as "CUnifSp";
  latexdef "CUnifSp" as "{\rm CUnifSp}";
htmldef "metUnif" as "metUnif";
  althtmldef "metUnif" as "metUnif";
  latexdef "metUnif" as "{\rm metUnif}";
htmldef "metUnifOLD" as "metUnif<SUB>OLD</SUB>";
  althtmldef "metUnifOLD" as "metUnif<SUB>OLD</SUB>";
  latexdef "metUnifOLD" as "{\rm metUnif}_{OLD}";
htmldef "/e" as " /<SUB>&#x1D452;</SUB> ";
  althtmldef "/e" as " /<SUB>&#x1D452;</SUB> ";
  latexdef "/e" as '/_e';
htmldef "sum*" as "&Sigma;<SUP>*</SUP>";
  althtmldef "sum*" as "&Sigma;<SUP>*</SUP>";
  latexdef "sum*" as "\Sigma^*";
htmldef "oFC" as "&#8728;<SUB>&#x1D453;/&#x1D450;</SUB>";
  althtmldef "oFC" as "&#8728;<SUB>&#x1D453;/&#x1D450;</SUB>";
  latexdef "oFC" as "\circ_f/c";
htmldef "sigAlgebra" as "sigAlgebra";
  althtmldef "sigAlgebra" as "sigAlgebra";
  latexdef "sigAlgebra" as "{\rm sigAlgebra}";
htmldef "sigaGen" as "sigaGen";
  althtmldef "sigaGen" as "sigaGen";
  latexdef "sigaGen" as "{\rm sigaGen}";
htmldef "BrSiga" as "&#x1D505;<SUB>&#8477;</SUB>";
  althtmldef "BrSiga" as "&#x1D505;<SUB>&#8477;</SUB>";
  latexdef "BrSiga" as "\mathfrak{B}_\mathbb{R}";
htmldef "sX" as " &times;<SUB>s</SUB> ";
  althtmldef "sX" as " &times;<SUB>s</SUB> ";
  latexdef "sX" as "\times_s";
htmldef "measures" as "measures";
  althtmldef "measures" as "measures";
  latexdef "measures" as "{\rm measures}";
htmldef "MblFnM" as "MblFnM";
  althtmldef "MblFnM" as "MblFnM";
  latexdef "MblFnM" as "{\rm MblFnM}";
htmldef "ae" as "a.e.";
  althtmldef "ae" as "a.e.";
  latexdef "ae" as "{\rm a.e.}";
htmldef "~ae" as "~ a.e.";
  althtmldef "~ae" as "~ a.e.";
  latexdef "~ae" as "{\rm ~ a.e.}";
htmldef "QQHom" as "QQHom";
  althtmldef "QQHom" as "&#8474;Hom";
  latexdef "QQHom" as "\mathbb{Q}{\rm Hom}";
htmldef "RRHom" as "RRHom";
  althtmldef "RRHom" as "&#8477;Hom";
  latexdef "RRHom" as "\mathbb{R}{\rm Hom}";
htmldef "RR*Hom" as "RR<SUP>*</SUP>Hom";
  althtmldef "RR*Hom" as "&#8477;<SUP>*</SUP>Hom";
  latexdef "RR*Hom" as "\mathbb{R}^*{\rm Hom}";
htmldef "itgm" as "itgm";
  althtmldef "itgm" as "itgm";
  latexdef "itgm" as "{\rm itgm}";
htmldef "sitg" as "sitg";
  althtmldef "sitg" as "sitg";
  latexdef "sitg" as "{\rm sitg}";
htmldef "sitm" as "sitm";
  althtmldef "sitm" as "sitm";
  latexdef "sitm" as "{\rm sitm}";
htmldef "Prob" as "Prob";
  althtmldef "Prob" as "Prob";
  latexdef "Prob" as "{\rm Prob}";
htmldef "cprob" as "cprob";
  althtmldef "cprob" as "cprob";
  latexdef "cprob" as "{\rm cprob}";
htmldef "rRndVar" as "rRndVar";
  althtmldef "rRndVar" as "rRndVar";
  latexdef "rRndVar" as "{\rm rRndVar}";
htmldef "_Ind" as "&#x1D7ED;";
  althtmldef "_Ind" as "&#x1D7ED;";
  latexdef "_Ind" as "\mathsfbf{1}";
htmldef "oRVC" as "&#8728;<SUB>RV/&#x1D450;</SUB>";
  althtmldef "oRVC" as "&#8728;<SUB>RV/&#x1D450;</SUB>";
  latexdef "oRVC" as "\circ_RV/c";
/* End of Thierry Arnoux's mathbox */

/* Mathbox of Mario Carneiro */
htmldef "zeta" as
    "<IMG SRC='zeta.gif' WIDTH=9 HEIGHT=19 ALT=' zeta' TITLE='zeta'>";
  althtmldef "zeta" as "&zeta;";
  latexdef "zeta" as "\zeta";
htmldef "_G" as
    "<IMG SRC='cgamma.gif' WIDTH=10 HEIGHT=19 ALT=' _G' TITLE='_G'>";
  althtmldef "_G" as "&Gamma;";
  latexdef "_G" as "\Gamma";
htmldef "log_G" as
    "<IMG SRC='_log.gif' WIDTH=20 HEIGHT=19 ALT=' log' TITLE='log'> " +
    "<IMG SRC='cgamma.gif' WIDTH=10 HEIGHT=19 ALT=' _G' TITLE='_G'>";
  althtmldef "log_G" as "log &Gamma;";
  latexdef "log_G" as "\log\Gamma";
htmldef "1/_G" as
    "1/<IMG SRC='cgamma.gif' WIDTH=10 HEIGHT=19 ALT=' _G' TITLE='_G'>";
  althtmldef "1/_G" as "1/&Gamma;";
  latexdef "1/_G" as "1/\Gamma";
htmldef "Retr" as " Retr "; althtmldef "Retr" as " Retr ";
  latexdef "Retr" as "{\rm Retr}";
htmldef "PCon" as "PCon"; althtmldef "PCon" as "PCon";
  latexdef "PCon" as " {\rm PCon} ";
htmldef "SCon" as "SCon"; althtmldef "SCon" as "SCon";
  latexdef "SCon" as "{\rm SCon}";
htmldef "CovMap" as " CovMap "; althtmldef "CovMap" as " CovMap ";
  latexdef "CovMap" as " {\rm CovMap} ";
htmldef "EulPaths" as " EulPaths "; althtmldef "EulPaths" as " EulPaths ";
  latexdef "EulPaths" as " {\rm EulPaths} ";
htmldef "e.g" as
    " <IMG SRC='_ing.gif' WIDTH=17 HEIGHT=19 ALT=' e.g' TITLE='e.g'> ";
  althtmldef "e.g" as "&isin;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "e.g" as "\in_g";
htmldef "|g" as
    " <IMG SRC='barwedge.gif' WIDTH=9 HEIGHT=19 ALT=' |' TITLE='|'>" +
    "<IMG SRC='subg.gif' WIDTH=7 HEIGHT=19 ALT=' g' TITLE='g'> ";
  althtmldef "|g" as "&#8892;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|g" as "\barwedge_g";
htmldef "A.g" as
    "<IMG SRC='_forallg.gif' WIDTH=14 HEIGHT=19 ALT=' A.g' TITLE='A.g'>";
  althtmldef "A.g" as
    "&forall;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "A.g" as "\forall_g";
htmldef "=g" as
    " <IMG SRC='_eqg.gif' WIDTH=19 HEIGHT=19 ALT=' =g' TITLE='=g'> ";
  althtmldef "=g" as "=<SUB>&#x1D454;</SUB>"; latexdef "=g" as "=_g";
htmldef "/\g" as
    " <IMG SRC='_wedgeg.gif' WIDTH=18 HEIGHT=19 ALT=' /\g' TITLE='/\g'> ";
  althtmldef "/\g" as "&and;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "/\g" as "\wedge_g";
htmldef "-.g" as
    "<IMG SRC='_lnotg.gif' WIDTH=17 HEIGHT=19 ALT=' -.g' TITLE='-.g'>";
  althtmldef "-.g" as "&not;<SUB>&#x1D454;</SUB>"; latexdef "-.g" as "\lnot_g";
htmldef "->g" as
    " <IMG SRC='_tog.gif' WIDTH=20 HEIGHT=19 ALT=' -&gt;g' TITLE='-&gt;g'> ";
  althtmldef "->g" as
    " &rarr;<SUB>&#x1D454;</SUB> "; latexdef "->g" as "\to_g";
htmldef "<->g" as " <IMG SRC='_lrarrg.gif' WIDTH=20 HEIGHT=19 " +
    "ALT=' &lt;-&gt;g' TITLE='&lt;-&gt;g'> ";
  althtmldef "<->g" as " &harr;<SUB>&#x1D454;</SUB> ";
  latexdef "<->g" as "\leftrightarrow_g";
htmldef "\/g" as
    " <IMG SRC='_veeg.gif' WIDTH=15 HEIGHT=19 ALT=' \/g' TITLE='\/g'> ";
  althtmldef "\/g" as " &or;<SUB>&#x1D454;</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/g" as "\vee_g";
htmldef "E.g" as
    "<IMG SRC='_existsg.gif' WIDTH=16 HEIGHT=19 ALT=' E.g' TITLE='E.g'>";
  althtmldef "E.g" as
    "&exist;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "E.g" as "\exists_g";
htmldef "Fmla" as
    "<IMG SRC='_fmla.gif' WIDTH=33 HEIGHT=19 ALT=' Fmla' TITLE='Fmla'>";
  althtmldef "Fmla" as "Fmla"; latexdef "Fmla" as "{\rm Fmla}";
htmldef "Sat" as
    " <IMG SRC='_sat.gif' WIDTH=22 HEIGHT=19 ALT=' Sat' TITLE='Sat'> ";
  althtmldef "Sat" as " Sat "; latexdef "Sat" as "{\rm Sat}";
htmldef "SatE" as
    " <IMG SRC='_sat.gif' WIDTH=22 HEIGHT=19 ALT=' Sat' TITLE='Sat'>" +
    "<IMG SRC='subin.gif' WIDTH=7 HEIGHT=19 ALT=' E' TITLE='E'> ";
  althtmldef "SatE" as " Sat<SUB>&isin;</SUB> ";
  latexdef "SatE" as "{\rm Sat}_\in";
htmldef "|=" as
    " <IMG SRC='models.gif' WIDTH=12 HEIGHT=19 ALT=' |=' TITLE='|='> ";
  althtmldef "|=" as "&#8871;"; latexdef "|=" as "\models";
htmldef "AxExt" as
    "<IMG SRC='_axext.gif' WIDTH=41 HEIGHT=19 ALT=' AxExt' TITLE='AxExt'>";
  althtmldef "AxExt" as "AxExt"; latexdef "AxExt" as "{\rm AxExt}";
htmldef "AxRep" as
    "<IMG SRC='_axrep.gif' WIDTH=43 HEIGHT=19 ALT=' AxRep' TITLE='AxRep'>";
  althtmldef "AxRep" as "AxRep"; latexdef "AxRep" as "{\rm AxRep}";
htmldef "AxPow" as
    "<IMG SRC='_axpow.gif' WIDTH=46 HEIGHT=19 ALT=' AxPow' TITLE='AxPow'>";
  althtmldef "AxPow" as "AxPow"; latexdef "AxPow" as "{\rm AxPow}";
htmldef "AxUn" as
    "<IMG SRC='_axun.gif' WIDTH=36 HEIGHT=19 ALT=' AxUn' TITLE='AxUn'>";
  althtmldef "AxUn" as "AxUn"; latexdef "AxUn" as "{\rm AxUn}";
htmldef "AxReg" as
    "<IMG SRC='_axreg.gif' WIDTH=43 HEIGHT=19 ALT=' AxReg' TITLE='AxReg'>";
  althtmldef "AxReg" as "AxReg"; latexdef "AxReg" as "{\rm AxReg}";
htmldef "AxInf" as
    "<IMG SRC='_axinf.gif' WIDTH=36 HEIGHT=19 ALT=' AxInf' TITLE='AxInf'>";
  althtmldef "AxInf" as "AxInf"; latexdef "AxInf" as "{\rm AxInf}";
htmldef "ZF" as
    "<IMG SRC='_zf.gif' WIDTH=19 HEIGHT=19 ALT=' ZF' TITLE='ZF'>";
  althtmldef "ZF" as "<FONT FACE=sans-serif><B>ZF</B></FONT>";
  latexdef "ZF" as "{\sf ZF}";
htmldef "IntgRing" as " IntgRing "; althtmldef "IntgRing" as " IntgRing ";
  latexdef "IntgRing" as " {\rm IntgRing} ";
htmldef "cplMetSp" as " cplMetSp "; althtmldef "cplMetSp" as " cplMetSp ";
  latexdef "cplMetSp" as " {\rm cplMetSp} ";
htmldef "HomLimB" as " HomLimB "; althtmldef "HomLimB" as " HomLimB ";
  latexdef "HomLimB" as " {\rm HomLimB} ";
htmldef "HomLim" as " HomLim "; althtmldef "HomLim" as " HomLim ";
  latexdef "HomLim" as " {\rm HomLim} ";
htmldef "polyFld" as " polyFld "; althtmldef "polyFld" as " polyFld ";
  latexdef "polyFld" as " {\rm polyFld} ";
htmldef "splitFld1" as " splitFld<sub>1</sub> ";
  althtmldef "splitFld1" as " splitFld<sub>1</sub> ";
  latexdef "splitFld1" as " {\rm splitFld}_1 ";
htmldef "splitFld" as " splitFld "; althtmldef "splitFld" as " splitFld ";
  latexdef "splitFld" as " {\rm splitFld} ";
htmldef "polySplitLim" as " polySplitLim ";
  althtmldef "polySplitLim" as " polySplitLim ";
  latexdef "polySplitLim" as " {\rm polySplitLim} ";
htmldef "ZRing" as "ZRing"; althtmldef "ZRing" as "ZRing";
  latexdef "ZRing" as "{\rm ZRing}";
htmldef "GF" as " GF "; althtmldef "GF" as " GF ";
  latexdef "GF" as " {\rm GF} ";
htmldef "GF_oo" as "GF<sub>&infin;</sub>";
  althtmldef "GF_oo" as "GF<sub>&infin;</sub>";
  latexdef "GF_oo" as "{\rm GF}_\infty";
htmldef "~Qp" as "~Qp"; althtmldef "~Qp" as "~Qp";
  latexdef "~Qp" as "\sim_{\Bbb Qp}";
htmldef "/Qp" as "/Qp"; althtmldef "/Qp" as "/Qp";
  latexdef "/Qp" as "/_{\Bbb Qp}";
htmldef "Qp" as "Qp"; althtmldef "Qp" as "Qp";
  latexdef "Qp" as "\Bbb Q_p";
htmldef "Zp" as "Zp"; althtmldef "Zp" as "Zp";
  latexdef "Zp" as "\Bbb Z_p";
htmldef "_Qp" as "_Qp"; althtmldef "_Qp" as "_Qp";
  latexdef "_Qp" as "\overline{\Bbb Q_p}";
htmldef "Cp" as "Cp"; althtmldef "Cp" as "Cp";
  latexdef "Cp" as "\Bbb C_p";

/* End of Mario Carneiro's mathbox */

/* Mathbox of Paul Chapman */
/* End of Paul Chapman's mathbox */

/* Mathbox of Drahflow */
htmldef "^r" as
    "<IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' TITLE='^'>" +
    "<IMG SRC='r.gif' WIDTH=8 HEIGHT=19 ALT=' r' TITLE='r'>" ;
  althtmldef "^r" as '&uarr;r';
  latexdef "^r" as "\uparrow_r";
htmldef "t*rec" as "<IMG SRC='t.gif' WIDTH=7 HEIGHT=19 ALT=' t' TITLE='t'>" +
    "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT=' *' TITLE='*'>" + "rec";
  althtmldef "t*rec" as "t*rec";
  latexdef "t*rec" as "{{\rm t}*}_{\rm rec}";
/* End of Drahflow's mathbox */

/* Mathbox of Scott Fenton */
htmldef "Pred" as
    "<IMG SRC='_pred.gif' WIDTH=30 HEIGHT=19 ALT=' Pred' TITLE='Pred'>";
  althtmldef "Pred" as "Pred";
  latexdef "Pred" as "{\rm Pred}";
htmldef "TrPred" as
    "<IMG SRC='_trpred.gif' WIDTH=44 HEIGHT=19 ALT=' TrPred' TITLE='TrPred'>";
  althtmldef "TrPred" as "TrPred";
  latexdef "TrPred" as "{\rm TrPred}";
htmldef "wrecs" as "wrecs";
  althtmldef "wrecs" as "wrecs";
  latexdef "wrecs" as "{\rm wrecs}";
htmldef "wsuc" as "wsuc";
  althtmldef "wsuc" as "wsuc";
  latexdef "wsuc" as "{\rm wsuc}";
htmldef "WLim" as "WLim";
  althtmldef "WLim" as "WLim";
  latexdef "WLim" as "{\rm WLim}";
htmldef "No" as "<IMG SRC='_no.gif' WIDTH=17 HEIGHT=19 ALT=' No' TITLE='No'>";
  althtmldef "No" as '<FONT FACE=sans-serif> No </FONT>';
  latexdef "No" as "{\rm No}";
htmldef "<s" as
    "<IMG SRC='lt.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;' TITLE='&lt;'>" +
    "<IMG SRC='subs.gif' WIDTH=6 HEIGHT=19 ALT=' s' TITLE='s'>";
  althtmldef "<s" as " &lt;s ";
  latexdef "<s" as "{<_s}";
htmldef "bday" as
    "<IMG SRC='_bday.gif' WIDTH=32 HEIGHT=19 ALT=' bday' TITLE='bday'>";
  althtmldef "bday" as '<FONT FACE=sans-serif> bday </FONT>';
  latexdef "bday" as "{\rm bday}";
htmldef "(++)" as "(++)";
  althtmldef "(++)" as "(++)";
  latexdef "(++)" as "(++)";
htmldef "(x)" as
    " <IMG SRC='otimes.gif' WIDTH=13 HEIGHT=19 ALT=' (x)' TITLE='(x)'> ";
  althtmldef "(x)" as " &#x2297; ";
  latexdef "(x)" as "\otimes";
/*
htmldef "(+)" as
    " <IMG SRC='oplus.gif' WIDTH=13 HEIGHT=19 ALT=' (+)' TITLE='(+)'> ";
  althtmldef "(+)" as " &#x2295; ";
  latexdef "(+)" as "\oplus";
*/
htmldef "Bigcup" as
    "<IMG SRC='_bigcup.gif' WIDTH=44 HEIGHT=19 ALT=' Bigcup' TITLE='Bigcup'>";
  althtmldef "Bigcup" as '<FONT FACE=sans-serif> Bigcup </FONT>';
  latexdef "Bigcup" as "{\rm Bigcup}";
htmldef "SSet" as
    "<IMG SRC='_sset.gif' WIDTH=29 HEIGHT=19 ALT=' SSet' TITLE='SSet'>";
  althtmldef "SSet" as '<FONT FACE=sans-serif> SSet </FONT>';
  latexdef "SSet" as "{\rm SSet}";
htmldef "Trans" as
    "<IMG SRC='_trans.gif' WIDTH=38 HEIGHT=19 ALT=' Trans' TITLE='Trans'>";
  althtmldef "Trans" as '<FONT FACE=sans-serif> Trans </FONT>';
  latexdef "Trans" as "{\rm Trans}";
htmldef "Limits" as
    "<IMG SRC='_limits.gif' WIDTH=41 HEIGHT=19 ALT=' Limits' TITLE='Limits'>";
  althtmldef "Limits" as '<FONT FACE=sans-serif> Limits </FONT>';
  latexdef "Limits" as "{\rm Limits}";
htmldef "Fix" as
    "<IMG SRC='_fix.gif' WIDTH=21 HEIGHT=19 ALT=' Fix' TITLE='Fix'>";
  althtmldef "Fix" as '<FONT FACE=sans-serif> Fix </FONT>';
  latexdef "Fix" as "{\rm Fix}";
htmldef "Funs" as
    "<IMG SRC='_funs.gif' WIDTH=31 HEIGHT=19 ALT=' Funs' TITLE='Funs'>";
  althtmldef "Funs" as '<FONT FACE=sans-serif> Funs </FONT>';
  latexdef "Funs" as "{\rm Funs}";
htmldef "Singleton" as "Singleton";
  althtmldef "Singleton" as "Singleton";
  latexdef "Singleton" as "Singleton";
htmldef "Singletons" as "<IMG SRC='_singletons.gif' WIDTH=66 HEIGHT=19 " +
    "ALT=' Singletons' TITLE='Singletons'>";
  althtmldef "Singletons" as '<FONT FACE=sans-serif> Singletons </FONT>';
  latexdef "Singletons" as "{\rm Singletons}";
htmldef "Image" as "Image";
  althtmldef "Image" as "Image";
  latexdef "Image" as "{\rm Image}";
htmldef "Cart" as "Cart";
  althtmldef "Cart" as "Cart";
  latexdef "Cart" as "{\rm Cart}";
htmldef "Img" as "Img";
  althtmldef "Img" as "Img";
  latexdef "Img" as "{\rm Img}";
htmldef "Domain" as "Domain";
  althtmldef "Domain" as "Domain";
  latexdef "Domain" as "{\rm Domain}";
htmldef "Range" as "Range";
  althtmldef "Range" as "Range";
  latexdef "Range" as "{\rm Range}";
htmldef "pprod" as "pprod";
  althtmldef "pprod" as "pprod";
  latexdef "pprod" as "{\rm pprod}";
htmldef "Apply" as "Apply";
  althtmldef "Apply" as "Apply";
  latexdef "Apply" as "{\rm Apply}";
htmldef "Cup" as "Cup";
  althtmldef "Cup" as "Cup";
  latexdef "Cup" as "{\rm Cup}";
htmldef "Cap" as "Cap";
  althtmldef "Cap" as "Cap";
  latexdef "Cap" as "{\rm Cap}";
htmldef "Succ" as "Succ";
  althtmldef "Succ" as "Succ";
  latexdef "Succ" as "{\rm Succ}";
htmldef "Funpart" as "Funpart";
  althtmldef "Funpart" as "Funpart";
  latexdef "Funpart" as "{\rm Funpart}";
htmldef "FullFun" as "FullFun";
  althtmldef "FullFun" as "FullFun";
  latexdef "FullFun" as "{\rm FullFun}";
htmldef "Restrict" as "Restrict";
  althtmldef "Restrict" as "Restrict";
  latexdef "Restrict" as "{\rm Restrict}";
htmldef "LB" as "LB";
  althtmldef "LB" as "LB";
  latexdef "LB" as "{\rm LB}";
htmldef "UB" as "UB";
  althtmldef "UB" as "UB";
  latexdef "UB" as "{\rm UB}";
htmldef "<<" as
  "<IMG SRC='llangle.gif' WIDTH=6 HEIGHT=19 ALT=' &lt;&lt;' TITLE='&lt;&lt;'>";
  althtmldef "<<" as "&#10218;";
  latexdef "<<" as "\langle\langle";
htmldef ">>" as
  "<IMG SRC='rrangle.gif' WIDTH=6 HEIGHT=19 ALT=' &gt;&gt;' TITLE='&gt;&gt;'>";
  althtmldef ">>" as "&#10219;";
  latexdef ">>" as "\rangle\rangle";
htmldef "XX." as
    " <IMG SRC='_ttimes.gif' WIDTH=18 HEIGHT=19 ALT=' XX.' TITLE='XX.'> ";
  althtmldef "XX." as ' &times;&times; ';
  latexdef "XX." as "\times\times";
htmldef "EE" as "<IMG SRC='bbe.gif' WIDTH=11 HEIGHT=19 ALT=' EE' TITLE='EE'>";
  althtmldef "EE" as " &#x1D53C ";
/*
htmldef "EE" as " <FONT FACE=sans-serif>&Eopf;</FONT> ";
  althtmldef "EE" as " <FONT FACE=sans-serif>&#x1D53C</FONT> ";
*/
  latexdef "EE" as "\mathbb{E}";
htmldef "Btwn" as
    " <IMG SRC='_btwn.gif' WIDTH=35 HEIGHT=19 ALT=' Btwn' TITLE='Btwn'> ";
  althtmldef "Btwn" as " Btwn ";
  latexdef "Btwn" as "{\rm Btwn}";
htmldef "Cgr" as "Cgr";
  althtmldef "Cgr" as "Cgr";
  latexdef "Cgr" as "{\rm Cgr}";
htmldef "OuterFiveSeg" as " <IMG SRC='_outerfiveseg.gif' WIDTH=89 HEIGHT=19 " +
    "ALT=' OuterFiveSeg' TITLE='OuterFiveSeg'> ";
  althtmldef "OuterFiveSeg" as " OuterFiveSeg ";
  latexdef "OuterFiveSeg" as "{\bb OuterFiveSeg}";
htmldef "TransportTo" as "TransportTo";
  althtmldef "TransportTo" as "TransportTo";
  latexdef "TransportTo" as "{\rm TransportTo}";
htmldef "InnerFiveSeg" as " <IMG SRC='_innerfiveseg.gif' WIDTH=84 HEIGHT=19 " +
    "ALT=' InnerFiveSeg' TITLE='InnerFiveSeg'> ";
  althtmldef "InnerFiveSeg" as " InnerFiveSeg ";
  latexdef "InnerFiveSeg" as "{\bb InnerFiveSeg}";
htmldef "Cgr3" as "Cgr3";
  althtmldef "Cgr3" as "Cgr3";
  latexdef "Cgr3" as "{\rm Cgr3}";
htmldef "Colinear" as " <IMG SRC='_colinear.gif' WIDTH=54 HEIGHT=19 " +
    "ALT=' Colinear' TITLE='Colinear'> ";
  althtmldef "Colinear" as " Colinear ";
  latexdef "Colinear" as "{\bb Colinear}";
htmldef "FiveSeg" as " <IMG SRC='_fiveseg.gif' WIDTH=51 HEIGHT=19 " +
    "ALT=' FiveSeg' TITLE='FiveSeg'> ";
  althtmldef "FiveSeg" as " FiveSeg ";
  latexdef "FiveSeg" as "{\bb FiveSeg}";
/*
htmldef "==3" as
    " <IMG SRC='equiv.gif' WIDTH=12 HEIGHT=19 ALT=' ==' TITLE='=='>" +
    "<IMG SRC='sub3.gif' WIDTH=6 HEIGHT=19 ALT=' 3' TITLE='3'> ";
  althtmldef "==3" as " &#x2261;&#x2083; ";
  latexdef "==3" as "\equiv_3";
*/
htmldef "Seg<_" as " <IMG SRC='_segle.gif' WIDTH=30 HEIGHT=19 " +
    "ALT=' Seg&lt;_' TITLE='Seg&lt;_'> ";
  althtmldef "Seg<_" as " Seg<SUB>&le;</SUB> ";
  latexdef "Seg<_" as "{\bb Seg}_\le";
htmldef "OutsideOf" as "OutsideOf";
  althtmldef "OutsideOf" as "OutsideOf";
  latexdef "OutsideOf" as "{\rm OutsideOf}";
htmldef "Line" as "Line";
  althtmldef "Line" as "Line";
  latexdef "Line" as "{\rm Line}";
htmldef "LinesEE" as "LinesEE";
  althtmldef "LinesEE" as "LinesEE";
  latexdef "LinesEE" as "{\rm LinesEE}";
htmldef "Ray" as "Ray";
  althtmldef "Ray" as "Ray";
  latexdef "Ray" as "{\rm Ray}";
htmldef "BernPoly" as " BernPoly ";
  althtmldef "BernPoly" as " BernPoly ";
  latexdef "BernPoly" as "{\rm BernPoly}";

htmldef "Hf" as " Hf ";
  althtmldef "Hf" as " Hf ";
  latexdef "Hf" as "{\rm Hf}";

htmldef "prod_" as "<IMG SRC='prod.gif' WIDTH=12 HEIGHT=19 " +
    "ALT=' prod_' TITLE='prod_'>";
  althtmldef "prod_" as "&#x220F";
  latexdef "prod_" as "\prod";

htmldef "FallFac" as " FallFac ";
  althtmldef "FallFac" as " FallFac ";
  latexdef "FallFac" as "{\rm FallFac}";

htmldef "RiseFac" as " RiseFac ";
  althtmldef "RiseFac" as " RiseFac ";
  latexdef "RiseFac" as "{\rm RiseFac}";

/* End of Scott Fenton's mathbox */


/* Mathbox of Jeff Hankins */

/* Mathbox of Anthony Hart */

/* Mathbox of Jeff Hoffman */
htmldef "gcdOLD" as
    "<IMG SRC='_gcd.gif' WIDTH=23 HEIGHT=19 ALT=' gcd' TITLE='gcd'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "gcdOLD" as " gcd<SUB>OLD</SUB> ";
  latexdef "gcdOLD" as "{\rm gcd_{OLD}}";


/***** Commented out to due to removal of FL's mathbox ******
       For recovery, note that "*" was changed to "@" everywhere.
/@ Mathbox of FL @/
htmldef "A1" as
    "<IMG SRC='_bnj_ca1.gif' WIDTH=16 HEIGHT=19 ALT=' A1' TITLE='A1'>";
  althtmldef "A1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;<SUB>1</SUB></SPAN>';
  latexdef "A1" as "A_1";
htmldef "A2" as "<IMG SRC='_ca.gif' WIDTH=11 HEIGHT=19 ALT=' A' TITLE='A'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "A2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;<SUB>2</SUB></SPAN>';
  latexdef "A2" as "A_2";
htmldef "B1" as
    "<IMG SRC='_bnj_cb1.gif' WIDTH=17 HEIGHT=19 ALT=' B1' TITLE='B1'>";
  althtmldef "B1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;<SUB>1</SUB></SPAN>';
  latexdef "B1" as "B_1";
htmldef "B2" as "<IMG SRC='_cb.gif' WIDTH=12 HEIGHT=19 ALT=' B' TITLE='B'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "B2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;<SUB>2</SUB></SPAN>';
  latexdef "B2" as "B_2";
htmldef "C1" as
    "<IMG SRC='_bnj_cc1.gif' WIDTH=17 HEIGHT=19 ALT=' C1' TITLE='C1'>";
  althtmldef "C1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;<SUB>1</SUB></SPAN>';
  latexdef "C1" as "C_1";
htmldef "C2" as "<IMG SRC='_cc.gif' WIDTH=12 HEIGHT=19 ALT=' C' TITLE='C'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "C2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;<SUB>2</SUB></SPAN>';
  latexdef "C2" as "C_2";
htmldef "D1" as
    "<IMG SRC='_bnj_cd1.gif' WIDTH=17 HEIGHT=19 ALT=' D1' TITLE='D1'>";
  althtmldef "D1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;<SUB>1</SUB></SPAN>';
  latexdef "D1" as "D_1";
htmldef "D2" as "<IMG SRC='_cd.gif' WIDTH=12 HEIGHT=19 ALT=' D' TITLE='D'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "D2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;<SUB>2</SUB></SPAN>';
  latexdef "D2" as "D_2";
htmldef "F1" as
    "<IMG SRC='_bnj_cf1.gif' WIDTH=18 HEIGHT=19 ALT=' F1' TITLE='F1'>";
  althtmldef "F1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;<SUB>1</SUB></SPAN>';
  latexdef "F1" as "F_1";
htmldef "F2" as "<IMG SRC='_cf.gif' WIDTH=13 HEIGHT=19 ALT=' F' TITLE='F'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "F2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;<SUB>2</SUB></SPAN>';
  latexdef "F2" as "F_2";
htmldef "F3" as "<IMG SRC='_cf.gif' WIDTH=13 HEIGHT=19 ALT=' F' TITLE='F'>" +
    "<IMG SRC='__sub3p.gif' WIDTH=6 HEIGHT=19 ALT=' 3' TITLE='3'>";
  althtmldef "F3" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;<SUB>3</SUB></SPAN>';
  latexdef "F3" as "F_3";
htmldef "G1" as
    "<IMG SRC='_bnj_cg1.gif' WIDTH=17 HEIGHT=19 ALT=' G1' TITLE='G1'>";
  althtmldef "G1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;<SUB>1</SUB></SPAN>';
  latexdef "G1" as "G_1";
htmldef "G2" as "<IMG SRC='_cg.gif' WIDTH=12 HEIGHT=19 ALT=' G' TITLE='G'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "G2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;<SUB>2</SUB></SPAN>';
  latexdef "G2" as "G_2";
htmldef "H1" as
    "<IMG SRC='_bnj_ch1.gif' WIDTH=19 HEIGHT=19 ALT=' H1' TITLE='H1'>";
  althtmldef "H1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;<SUB>1</SUB></SPAN>';
  latexdef "H1" as "H_1";
htmldef "H2" as "<IMG SRC='_ch.gif' WIDTH=14 HEIGHT=19 ALT=' H' TITLE='H'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "H2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;<SUB>2</SUB></SPAN>';
  latexdef "H2" as "H_2";
htmldef "I1" as
    "<IMG SRC='_bnj_ci1.gif' WIDTH=13 HEIGHT=19 ALT=' I1' TITLE='I1'>";
  althtmldef "I1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;<SUB>1</SUB></SPAN>';
  latexdef "I1" as "I_1";
htmldef "I2" as "<IMG SRC='_ci.gif' WIDTH=8 HEIGHT=19 ALT=' I' TITLE='I'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "I2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;<SUB>2</SUB></SPAN>';
  latexdef "I2" as "I_2";
htmldef "L1" as
    "<IMG SRC='_bnj_cl1.gif' WIDTH=15 HEIGHT=19 ALT=' L1' TITLE='L1'>";
  althtmldef "L1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;<SUB>1</SUB></SPAN>';
  latexdef "L1" as "L_1";
htmldef "L2" as "<IMG SRC='_cl.gif' WIDTH=10 HEIGHT=19 ALT=' L' TITLE='L'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "L2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;<SUB>2</SUB></SPAN>';
  latexdef "L2" as "L_2";
htmldef "L3" as "<IMG SRC='_cl.gif' WIDTH=10 HEIGHT=19 ALT=' L' TITLE='L'>" +
    "<IMG SRC='__sub3p.gif' WIDTH=6 HEIGHT=19 ALT=' 3' TITLE='3'>";
  althtmldef "L3" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;<SUB>3</SUB></SPAN>';
  latexdef "L3" as "L_3";
htmldef "M1" as
    "<IMG SRC='_bnj_cm1.gif' WIDTH=20 HEIGHT=19 ALT=' M1' TITLE='M1'>";
  althtmldef "M1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;<SUB>1</SUB></SPAN>';
  latexdef "M1" as "M_1";
htmldef "M2" as "<IMG SRC='_cm.gif' WIDTH=15 HEIGHT=19 ALT=' M' TITLE='M'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "M2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;<SUB>2</SUB></SPAN>';
  latexdef "M2" as "M_2";
htmldef "O1" as
    "<IMG SRC='_bnj_co1.gif' WIDTH=17 HEIGHT=19 ALT=' O1' TITLE='O1'>";
  althtmldef "O1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;<SUB>1</SUB></SPAN>';
  latexdef "O1" as "O_1";
htmldef "O2" as "<IMG SRC='_co.gif' WIDTH=12 HEIGHT=19 ALT=' O' TITLE='O'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "O2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;<SUB>2</SUB></SPAN>';
  latexdef "O2" as "O_2";
htmldef "Ro1" as "<IMG SRC='_cro.gif' WIDTH=19 HEIGHT=19 ALT=' Ro' TITLE='Ro'>"
    + "<IMG SRC='__sub1p.gif' WIDTH=4 HEIGHT=19 ALT=' 1' TITLE='1'>";
  althtmldef "Ro1" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>Ro<SUB>1</SUB></I></SPAN>';
  latexdef "Ro1" as "Ro_1";
htmldef "Ro2" as "<IMG SRC='_cro.gif' WIDTH=19 HEIGHT=19 ALT=' Ro' TITLE='Ro'>"
    + "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "Ro2" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>Ro<SUB>2</SUB></I></SPAN>';
  latexdef "Ro2" as "Ro_2";
htmldef "S1" as
    "<IMG SRC='_bnj_cs1.gif' WIDTH=16 HEIGHT=19 ALT=' S1' TITLE='S1'>";
  althtmldef "S1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;<SUB>1</SUB></SPAN>';
  latexdef "S1" as "S_1";
htmldef "S2" as "<IMG SRC='_cs.gif' WIDTH=11 HEIGHT=19 ALT=' S' TITLE='S'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "S2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;<SUB>2</SUB></SPAN>';
  latexdef "S2" as "S_2";
htmldef "V1" as
    "<IMG SRC='_bnj_cv1.gif' WIDTH=17 HEIGHT=19 ALT=' V1' TITLE='V1'>";
  althtmldef "V1" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;<SUB>1</SUB></SPAN>';
  latexdef "V1" as "V_1";
htmldef "V2" as "<IMG SRC='_cv.gif' WIDTH=12 HEIGHT=19 ALT=' V' TITLE='V'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "V2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;<SUB>2</SUB></SPAN>';
  latexdef "V2" as "V_2";
htmldef "V3" as "<IMG SRC='_cv.gif' WIDTH=12 HEIGHT=19 ALT=' V' TITLE='V'>" +
    "<IMG SRC='__sub3p.gif' WIDTH=6 HEIGHT=19 ALT=' 3' TITLE='3'>";
  althtmldef "V3" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;<SUB>2</SUB></SPAN>';
  latexdef "V3" as "V_3";
htmldef "W2" as "<IMG SRC='_cw.gif' WIDTH=16 HEIGHT=19 ALT=' W' TITLE='W'>" +
    "<IMG SRC='__sub2p.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "W2" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;<SUB>2</SUB></SPAN>';
  latexdef "W2" as "W_2";

htmldef "+t" as "<IMG SRC='_plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>"
    + "<IMG SRC='__subtp.gif' WIDTH=5 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "+t" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>+<SUB>t</SUB> </I></SPAN>';
  latexdef "+t" as "+_t";
htmldef "-t" as "<IMG SRC='_minus.gif' WIDTH=11 HEIGHT=19 ALT=' -' TITLE='-'>"
    + "<IMG SRC='__subtp.gif' WIDTH=5 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "-t" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>-<SUB>t</SUB> </I></SPAN>';
  latexdef "-t" as "-_t";
htmldef ".t" as "<IMG SRC='_cdot.gif' WIDTH=4 HEIGHT=19 ALT=' .' TITLE='.'>" +
    "<IMG SRC='__subtp.gif' WIDTH=5 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef ".t" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.<SUB>t</SUB> </I></SPAN>';
  latexdef ".t" as "._t";
htmldef "/t" as "<IMG SRC='_solidus.gif' WIDTH=6 HEIGHT=19 ALT=' /' " +
    "TITLE='/'><IMG SRC='__subtp.gif' WIDTH=5 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "/t" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>/<SUB>t</SUB> </I></SPAN>';
  latexdef "/t" as "/_t";
htmldef "~t" as "<IMG SRC='_sim.gif' WIDTH=13 HEIGHT=19 ALT=' ~' TITLE='~'>" +
    "<IMG SRC='__subtp.gif' WIDTH=5 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "~t" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>~<SUB>t</SUB> </I></SPAN>';
  latexdef "~t" as "~_t";
htmldef "0t" as "<IMG SRC='_0.gif' WIDTH=8 HEIGHT=19 ALT=' 0' TITLE='0'>" +
    "<IMG SRC='__subtp.gif' WIDTH=5 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "0t" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>0<SUB>t</SUB> </I></SPAN>';
  latexdef "0t" as "0_t";
htmldef "1t" as "<IMG SRC='_1.gif' WIDTH=7 HEIGHT=19 ALT=' 1' TITLE='1'>" +
    "<IMG SRC='__subtp.gif' WIDTH=5 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "1t" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>1<SUB>t</SUB> </I></SPAN>';
  latexdef "1t" as "1_t";

htmldef "+w" as "<IMG SRC='_plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>"
    + "<IMG SRC='__subwp.gif' WIDTH=7 HEIGHT=19 ALT=' w' TITLE='w'>";
  althtmldef "+w" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>+<SUB>w</SUB> </I></SPAN>';
  latexdef "+w" as "+_w";
htmldef "-w" as "<IMG SRC='_minus.gif' WIDTH=11 HEIGHT=19 ALT=' -' TITLE='-'>"
    + "<IMG SRC='__subwp.gif' WIDTH=7 HEIGHT=19 ALT=' w' TITLE='w'>";
  althtmldef "-w" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>-<SUB>w</SUB> </I></SPAN>';
  latexdef "-w" as "-_w";
htmldef ".w" as "<IMG SRC='_cdot.gif' WIDTH=4 HEIGHT=19 ALT=' .' TITLE='.'>" +
    "<IMG SRC='__subwp.gif' WIDTH=7 HEIGHT=19 ALT=' w' TITLE='w'>";
  althtmldef ".w" as
   '<SPAN CLASS=class STYLE="color:#C3C"><I>.<SUB>w</SUB> </I></SPAN>';
  latexdef ".w" as "._w";
htmldef "0w" as "<IMG SRC='_0.gif' WIDTH=8 HEIGHT=19 ALT=' 0' TITLE='0'>" +
    "<IMG SRC='__subwp.gif' WIDTH=7 HEIGHT=19 ALT=' w' TITLE='w'>";
  althtmldef "0w" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>0<SUB>w</SUB> </I></SPAN>';
  latexdef "0w" as "0_w";
htmldef "~w" as "<IMG SRC='_sim.gif' WIDTH=13 HEIGHT=19 ALT=' ~' TITLE='~'>" +
    "<IMG SRC='__subwp.gif' WIDTH=7 HEIGHT=19 ALT=' w' TITLE='w'>";
  althtmldef "~w" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>~<SUB>w</SUB> </I></SPAN>';
  latexdef "~w" as "~_w";
htmldef "<_a" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>&le<SUB>a</SUB> </I></SPAN>';
  althtmldef "<_a" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>&le;<SUB>a</SUB> </I></SPAN>';
  latexdef "<_a" as "\le";
htmldef "<_b" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>&le<SUB>b</SUB> </I></SPAN>';
  althtmldef "<_b" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>&le;<SUB>b</SUB> </I></SPAN>';
  latexdef "<_b" as "\le";

htmldef "o'" as "<IMG SRC='_bnj_oPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " o'_" + '"' + " TITLE=" + '"' + "o'_" + '"' + ">";
  althtmldef "o'" as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45C;&prime;</SPAN>';
  latexdef "o'"  as "o'";
htmldef "s'" as "<IMG SRC='_bnj_sPrime.gif' WIDTH=11 HEIGHT=19" +
    " ALT=" + '"' + " s'" + '"' + " TITLE=" + '"' + "s'" + '"' + ">";
  althtmldef "s'" as
    '<SPAN CLASS=set STYLE="color:red">&#x1D460;&prime;</SPAN>';
  latexdef "s'" as "s'";
htmldef "v'" as "<IMG SRC='_bnj_vPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " v'" + '"' + " TITLE=" + '"' + "v'" + '"' + ">";
  althtmldef "v'" as
    '<SPAN CLASS=set STYLE="color:red">&#x1D463;&prime;</SPAN>';
  latexdef "v'" as "v'";
htmldef 'o"' as "<IMG SRC='_bnj_oPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' o" + '"' + "'TITLE='o" + '"' + "'>";
  althtmldef 'o"' as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45C;&Prime;</SPAN>';
  latexdef 'o"' as "o''";
htmldef 's"' as "<IMG SRC='_bnj_sPrimePrime.gif' WIDTH=14 HEIGHT=19 " +
    " ALT=' s" + '"' + "'TITLE='s" + '"' + "'>";
  althtmldef 's"' as
    '<SPAN CLASS=set STYLE="color:red">&#x1D460;&Prime;</SPAN>';
  latexdef 's"' as "s''";
htmldef 'v"' as "<IMG SRC='_bnj_vPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' v" + '"' + "'TITLE='v" + '"' + "'>";
  althtmldef 'v"' as
    '<SPAN CLASS=set STYLE="color:red">&#x1D463;&Prime;</SPAN>';
  latexdef 'v"' as "v''";
htmldef "a0" as
    "<IMG SRC='_bnj_a0.gif' WIDTH=16 HEIGHT=19 ALT=' a0' TITLE='a0'>";
  althtmldef "a0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D44E;<SUB>0</SUB></SPAN>';
  latexdef "a0"  as "a_0";
htmldef "b0" as
    "<IMG SRC='_bnj_b0.gif' WIDTH=15 HEIGHT=19 ALT=' b0' TITLE='b0'>";
  althtmldef "b0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D44F;<SUB>0</SUB></SPAN>';
  latexdef "b0"  as "b_0";
htmldef "o0" as
    "<IMG SRC='_bnj_o0.gif' WIDTH=15 HEIGHT=19 ALT=' o0' TITLE='o0'>";
  althtmldef "o0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45C;<SUB>0</SUB></SPAN>';
  latexdef "o0"  as "o_0";
htmldef "a1" as
    "<IMG SRC='_bnj_a1.gif' WIDTH=14 HEIGHT=19 ALT=' a1' TITLE='a1'>";
  althtmldef "a1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D44E;<SUB>1</SUB></SPAN>';
  latexdef "a1"  as "a_1";
htmldef "b1" as
    "<IMG SRC='_bnj_b1.gif' WIDTH=13 HEIGHT=19 ALT=' b1' TITLE='b1'>";
  althtmldef "b1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D44F;<SUB>1</SUB></SPAN>';
  latexdef "b1"  as "b_1";
htmldef "o1" as
    "<IMG SRC='_bnj_o1.gif' WIDTH=13 HEIGHT=19 ALT=' o1' TITLE='o1'>";
  althtmldef "o1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45C;<SUB>1</SUB></SPAN>';
  latexdef "o1"  as "o_1";
htmldef "v2"  as "<IMG SRC='_v.gif' WIDTH=9 HEIGHT=19 ALT=' v' TITLE='v'>" +
    "<IMG SRC='__sub2r.gif' WIDTH=6 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "v2"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D463;<SUB>2</SUB></SPAN>';
  latexdef "v2"  as "v_2";

htmldef "[.]" as
    "<IMG SRC='wbox.gif' WIDTH=11 HEIGHT=19 ALT=' [.]' TITLE='[.]'>";
  althtmldef "[.]" as "&#9723;";
  latexdef "[.]" as "\Box";
htmldef "<>" as
    "<IMG SRC='wdiamond.gif' WIDTH=13 HEIGHT=19 " +
    "ALT=' &lt;&gt;' TITLE='&lt;&gt;'>";
  althtmldef "<>" as "&#9671;";
  latexdef "<>" as "\Diamond";
htmldef "()" as
    "<IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' ()' TITLE='()'>";
  althtmldef "()" as "&#9675;";
  latexdef "()" as "\bigcirc";
htmldef "until" as
    " <IMG SRC='_until.gif' WIDTH=30 HEIGHT=19 ALT=' until' TITLE='until'> ";
  althtmldef "until" as " until ";
  latexdef "until" as "{\rm until}";
htmldef "pr" as
    " <IMG SRC='_pr.gif' WIDTH=14 HEIGHT=19 ALT=' pr' TITLE='pr'> ";
  althtmldef "pr" as " pr ";
  latexdef "pr" as "{\rm pr}";
htmldef "prj" as
    " <IMG SRC='_prj.gif' WIDTH=17 HEIGHT=19 ALT=' prj' TITLE='prj'> ";
  althtmldef "prj" as " prj ";
  latexdef "prj" as "{\rm prj}";
htmldef "cset" as
    "<IMG SRC='_cset.gif' WIDTH=26 HEIGHT=19 ALT=' cset' TITLE='cset'>";
  althtmldef "cset" as "cset";
  latexdef "cset" as "{\rm cset}";
htmldef "LatAlg" as
    "<IMG SRC='_latalg.gif' WIDTH=45 HEIGHT=19 ALT=' LatAlg' TITLE='LatAlg'>";
  althtmldef "LatAlg" as "LatAlg";
  latexdef "LatAlg" as "{\rm LatAlg}";
htmldef "cur1" as
    "<IMG SRC='_cur1.gif' WIDTH=25 HEIGHT=19 ALT=' cur1' TITLE='cur1'>";
  althtmldef "cur1" as "cur1";
  latexdef "cur1" as "{\rm cur1}";
htmldef "cur2" as
    "<IMG SRC='_cur2.gif' WIDTH=27 HEIGHT=19 ALT=' cur2' TITLE='cur2'>";
  althtmldef "cur2" as "cur2";
  latexdef "cur2" as "{\rm cur2}";
htmldef "OrHom" as
    " <IMG SRC='_orhom.gif' WIDTH=46 HEIGHT=19 ALT=' OrHom' TITLE='OrHom'> ";
  althtmldef "OrHom" as " OrHom ";
  latexdef "OrHom" as "{\rm OrHom}";
htmldef "OrIso" as
    " <IMG SRC='_oriso.gif' WIDTH=34 HEIGHT=19 ALT=' OrIso' TITLE='OrIso'> ";
  althtmldef "OrIso" as " OrIso ";
  latexdef "OrIso" as "{\rm OrIso}";
htmldef "mxl" as
    "<IMG SRC='_mxl.gif' WIDTH=24 HEIGHT=19 ALT=' mxl' TITLE='mxl'>";
  althtmldef "mxl" as "mxl";
  latexdef "mxl" as "{\rm mxl}";
htmldef "mnl" as
    "<IMG SRC='_mnl.gif' WIDTH=24 HEIGHT=19 ALT=' mnl' TITLE='mnl'>";
  althtmldef "mnl" as "mnl";
  latexdef "mnl" as "{\rm mnl}";
htmldef "ub" as
    " <IMG SRC='_ub.gif' WIDTH=16 HEIGHT=19 ALT=' ub' TITLE='ub'> ";
  althtmldef "ub" as " ub ";
  latexdef "ub" as "{\rm ub}";
htmldef "lb" as "<IMG SRC='_lb.gif' WIDTH=12 HEIGHT=19 ALT=' lb' TITLE='lb'>";
  althtmldef "lb" as "lb";
  latexdef "lb" as "{\rm lb}";
htmldef "PresetRel" as "PresetRel";
  althtmldef "PresetRel" as "PresetRel";
  latexdef "PresetRel" as "{\rm PresetRel}";
htmldef "ge" as "<IMG SRC='_ge.gif' WIDTH=14 HEIGHT=19 ALT=' ge' TITLE='ge'>";
  althtmldef "ge" as "ge";
  latexdef "ge" as "{\rm ge}";
htmldef "leR" as "leR";
  althtmldef "leR" as "leR";
  latexdef "leR" as "{\rm leR}";
htmldef "AntiDir" as
    "<IMG SRC='_antidir.gif' WIDTH=48 HEIGHT=19 " +
    "ALT=' AntiDir' TITLE='AntiDir'>";
  althtmldef "AntiDir" as "AntiDir";
  latexdef "AntiDir" as "{\rm AntiDir}";
htmldef "BndLat" as
    "<IMG SRC='_bndlat.gif' WIDTH=48 HEIGHT=19 ALT=' BndLat' TITLE='BndLat'>";
  althtmldef "BndLat" as "BndLat";
  latexdef "BndLat" as "{\rm BndLat}";
htmldef "gprod_" as "<IMG SRC='prod.gif' WIDTH=12 HEIGHT=19 " +
    "ALT=' gprod_' TITLE='gprod_'>";
  althtmldef "gprod_" as "gprod_";
  latexdef "gprod_" as "\Pi";
htmldef "prod2_" as "<U>prod2</U>";
  althtmldef "prod2_" as "<U>prod2</U>";
  latexdef "prod2_" as "\underline{\rm prod2}";
htmldef "prod3_" as "<U>prod3</U>";
  althtmldef "prod3_" as "<U>prod3</U>";
  latexdef "prod3_" as "\underline{\rm prod3}";
htmldef "Com1" as
    "<IMG SRC='_com1.gif' WIDTH=33 HEIGHT=19 ALT=' Com1' TITLE='Com1'>";
  althtmldef "Com1" as "Com1";
  latexdef "Com1" as "{\rm Com1}";
htmldef "^md" as
    "<IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' TITLE='^'>" +
    "<IMG SRC='_submd.gif' WIDTH=17 HEIGHT=19 ALT=' md' TITLE='md'>";
  althtmldef "^md" as "^<SUB><I>md</I></SUB>";
  latexdef "^md" as "\uparrow_{md}";
htmldef "SubSemiGrp" as "<IMG SRC='_subsemigrp.gif' WIDTH=80 HEIGHT=19 " +
    "ALT=' SubSemiGrp' TITLE='SubSemiGrp'>";
  althtmldef "SubSemiGrp" as "SubSemiGrp";
  latexdef "SubSemiGrp" as "{\rm SubSemiGrp}";
htmldef "subSemiGrpGen" as " <IMG SRC='_subsemigrpgen.gif' " +
    "WIDTH=104 HEIGHT=19 ALT=' subSemiGrpGen' TITLE='subSemiGrpGen'> ";
  althtmldef "subSemiGrpGen" as "subSemiGrpGen";
  latexdef "subSemiGrpGen" as "{\rm subSemiGrpGen}";
htmldef "SemiGrpHom" as "<IMG SRC='_semigrphom.gif' WIDTH=85 HEIGHT=19 " +
    "ALT=' SemiGrpHom' TITLE='SemiGrpHom'>";
  althtmldef "SemiGrpHom" as "SemiGrpHom";
  latexdef "SemiGrpHom" as "{\rm SemiGrpHom}";
htmldef "FreeSemiGrp" as "<IMG SRC='_freesemigrp.gif' WIDTH=85 HEIGHT=19 " +
    "ALT=' FreeSemiGrp' TITLE='FreeSemiGrp'>";
  althtmldef "FreeSemiGrp" as "FreeSemiGrp";
  latexdef "FreeSemiGrp" as "{\rm FreeSemiGrp}";
htmldef "Tofld" as
    " <IMG SRC='_tofld.gif' WIDTH=33 HEIGHT=19 ALT=' Tofld' TITLE='Tofld'> ";
  althtmldef "Tofld" as " Tofld ";
  latexdef "Tofld" as "{\rm Tofld}";
htmldef "zeroDiv" as
    " <IMG SRC='_zerodiv.gif' WIDTH=48 HEIGHT=19 " +
    "ALT=' zeroDiv' TITLE='zeroDiv'> ";
  althtmldef "zeroDiv" as " zeroDiv ";
  latexdef "zeroDiv" as "{\rm zeroDiv}";
htmldef "IdlNEW" as "IdlNEW";
  althtmldef "IdlNEW" as "IdlNEW";
  latexdef "IdlNEW" as "{\rm IdlNEW}";
htmldef "Action" as
    "<IMG SRC='_action.gif' WIDTH=41 HEIGHT=19 ALT=' Action' TITLE='Action'>";
  althtmldef "Action" as "Action";
  latexdef "Action" as "{\rm Action}";
/@
htmldef "GrpWOp" as
    "<IMG SRC='_grpwop.gif' WIDTH=59 HEIGHT=19 ALT=' GrpWOp' TITLE='GrpWOp'>";
  althtmldef "GrpWOp" as "GrpWOp";
  latexdef "GrpWOp" as "{\rm GrpWOp}";
@/
htmldef "Vec" as
    " <IMG SRC='_vec.gif' WIDTH=22 HEIGHT=19 ALT=' Vec' TITLE='Vec'> ";
  althtmldef "Vec" as " Vec ";
  latexdef "Vec" as "{\rm Vec}";
htmldef "SubVec" as
    "<IMG SRC='_subvec.gif' WIDTH=44 HEIGHT=19 ALT=' SubVec' TITLE='SubVec'>";
  althtmldef "SubVec" as "SubVec";
  latexdef "SubVec" as "{\rm SubVec}";
htmldef "RVec" as
    " <IMG SRC='_rvec.gif' WIDTH=34 HEIGHT=19 ALT=' RVec' TITLE='RVec'> ";
  althtmldef "RVec" as " RVec ";
  latexdef "RVec" as "{\rm RVec}";
htmldef "+m" as "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='subm.gif' WIDTH=10 HEIGHT=19 ALT=' m' TITLE='m'>";
  althtmldef "+m" as "+<SUB>&#x1D45A;</SUB>";
  latexdef "+m" as "+_{m}";
htmldef "xm" as "<IMG SRC='times.gif' WIDTH=9 HEIGHT=19 ALT=' x' TITLE='x'>" +
    "<IMG SRC='subm.gif' WIDTH=10 HEIGHT=19 ALT=' m' TITLE='m'>";
  althtmldef "xm" as " &times;<SUB>&#x1D45A;</SUB> ";
  latexdef "xm" as "\times_{m}";
htmldef ".m" as "<IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' x' TITLE='x'>" +
    "<IMG SRC='subm.gif' WIDTH=10 HEIGHT=19 ALT=' m' TITLE='m'>";
  althtmldef ".m" as " &middot;<SUB>&#x1D45A;</SUB> ";
  latexdef ".m" as "\cdot_{m}";
htmldef "RAffSp" as
   " <IMG SRC='_raffsp.gif' WIDTH=48 HEIGHT=19 ALT=' RAffSp' TITLE='RAffSp'> ";
  althtmldef "RAffSp" as " RAffSp ";
  latexdef "RAffSp" as "{\rm RAffSp}";
/@
htmldef "dst" as "dst";
  althtmldef "dst" as "dst";
  latexdef "dst" as "{\rm dst}";
htmldef "absv" as "absv";
  althtmldef "absv" as "absv";
  latexdef "absv" as "{\rm absv}";
htmldef "nrm" as "nrm";
  althtmldef "nrm" as "nrm";
  latexdef "nrm" as "{\rm nrm}";
@/
htmldef "topX" as
    " <IMG SRC='_topx.gif' WIDTH=31 HEIGHT=19 ALT=' topX' TITLE='topX'> ";
  althtmldef "topX" as " topX ";
  latexdef "topX" as "{\rm topX}";
htmldef "fLimfrs" as " <IMG SRC='_flimfrs.gif' WIDTH=49 HEIGHT=19 " +
    "ALT=' fLimfrs' TITLE='fLimfrs'> ";
  althtmldef "fLimfrs" as " fLimfrs ";
  latexdef "fLimfrs" as "fLimfrs";
htmldef "IsolatedPt" as "<IMG SRC='_isolatedpt.gif' WIDTH=65 HEIGHT=19 " +
    "ALT=' IsolatedPt' TITLE='IsolatedPt'>";
  althtmldef "IsolatedPt" as "IsolatedPt";
  latexdef "IsolatedPt" as "IsolatedPt";
htmldef "UnifSpOLD" as
    "<IMG SRC='_unifsp.gif' WIDTH=44 HEIGHT=19 ALT=' UnifSp' TITLE='UnifSp'>";
  althtmldef "UnifSpOLD" as "UnifSp";
  latexdef "UnifSpOLD" as "{\rm UnifSp}";
htmldef "opfn" as
    " <IMG SRC='_opfn.gif' WIDTH=29 HEIGHT=19 ALT=' opfn' TITLE='opfn'> ";
  althtmldef "opfn" as " opfn ";
  latexdef "opfn" as "{\rm opfn}";
htmldef "TopFld" as
    "<IMG SRC='_topfld.gif' WIDTH=44 HEIGHT=19 ALT=' TopFld' TITLE='TopFld'>";
  althtmldef "TopFld" as " TopFld ";
  latexdef "TopFld" as "{\rm TopFld}";
htmldef "sup_" as
    " <IMG SRC='_sup.gif' WIDTH=22 HEIGHT=19 ALT=' sup' TITLE='sup'>" +
    "<IMG SRC='subminus.gif' WIDTH=9 HEIGHT=19 ALT=' _' TITLE='_'> ";
  althtmldef "sup_" as " sup_ ";
  latexdef "sup_" as "{\rm sup}_{-}";
htmldef "inf_" as
    " <IMG SRC='_inf.gif' WIDTH=18 HEIGHT=19 ALT=' inf' TITLE='inf'>" +
    "<IMG SRC='subminus.gif' WIDTH=9 HEIGHT=19 ALT=' _' TITLE='_'> ";
  althtmldef "inf_" as " inf_ ";
  latexdef "inf_" as "{\rm inf}_{-}";
htmldef "Frf" as
    "<IMG SRC='_frf.gif' WIDTH=21 HEIGHT=19 ALT=' Frf' TITLE='Frf'>";
  althtmldef "Frf" as "Frf";
  latexdef "Frf" as "{\rm Frf}";
htmldef "+cv" as " <IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' " +
    "TITLE='+'><IMG SRC='_subcv.gif' WIDTH=12 HEIGHT=19 ALT=' cv' " +
    "TITLE='cv'>";
  althtmldef "+cv" as "+cv";
  latexdef "+cv" as "+_{cv}";
htmldef "0cv" as "<IMG SRC='0.gif' WIDTH=8 HEIGHT=19 ALT=' 0' TITLE='0'>" +
    "<IMG SRC='_subcv.gif' WIDTH=12 HEIGHT=19 ALT=' cv' TITLE='cv'>";
  althtmldef "0cv" as "0cv";
  latexdef "0cv" as "0_{cv}";
htmldef "-cv" as " <IMG SRC='minus.gif' WIDTH=11 HEIGHT=19 ALT=' -' " +
   "TITLE='-'><IMG SRC='_subcv.gif' WIDTH=12 HEIGHT=19 ALT=' cv' TITLE='cv'> ";
  althtmldef "-cv" as " -<SUB><I>cv</I></SUB> ";
  latexdef "-cv" as "-_{cv}";
htmldef "-ucv" as
    "<IMG SRC='shortminus.gif' WIDTH=8 HEIGHT=19 ALT=' -' TITLE='-'>" +
    "<IMG SRC='_subcv.gif' WIDTH=12 HEIGHT=19 ALT=' cv' TITLE='cv'>";
  althtmldef "-ucv" as "-<SUB><I>cv</I></SUB>";
  latexdef "-ucv" as "-u_{cv}";
htmldef ".cv" as "<IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' .' TITLE='.'>" +
    "<IMG SRC='_subcv.gif' WIDTH=12 HEIGHT=19 ALT=' cv' TITLE='cv'>";
  althtmldef ".cv" as "&middot;<SUB><I>cv</I></SUB>";
  latexdef ".cv" as "\cdot_{cv}";
htmldef "/cv" as "<IMG SRC='solidus.gif' WIDTH=6 HEIGHT=19 ALT=' /' " +
    "TITLE='/'><IMG SRC='_subcv.gif' WIDTH=12 HEIGHT=19 ALT=' cv' TITLE='cv'>";
  althtmldef "/cv" as "/<SUB><I>cv</I></SUB>";
  latexdef "/cv" as "/_{cv}";
htmldef "Intvl" as
    "<IMG SRC='_intvl.gif' WIDTH=29 HEIGHT=19 ALT=' Intvl' TITLE='Intvl'>";
  althtmldef "Intvl" as "Intvl";
  latexdef "Intvl" as "{\rm Intvl}";
htmldef "der" as
    "<IMG SRC='_der.gif' WIDTH=21 HEIGHT=19 ALT=' der' TITLE='der'>";
  althtmldef "der" as "der";
  latexdef "der" as "{\rm der}";
htmldef "Dgra" as
    "<IMG SRC='_dgra.gif' WIDTH=33 HEIGHT=19 ALT=' Dgra' TITLE='Dgra'>";
  althtmldef "Dgra" as " Dgra ";
  latexdef "Dgra" as "{\rm Dgra}";
htmldef "Alg" as
    " <IMG SRC='_alg.gif' WIDTH=22 HEIGHT=19 ALT=' Alg' TITLE='Alg'> ";
  althtmldef "Alg" as " Alg ";
  latexdef "Alg" as "{\rm Alg}";
htmldef "dom_" as
    "<IMG SRC='_domu.gif' WIDTH=26 HEIGHT=19 ALT=' dom_' TITLE='dom_'>";
  althtmldef "dom_" as "<U>dom</U>";
  latexdef "dom_" as "\underline{\rm dom}";
htmldef "cod_" as
    "<IMG SRC='_codu.gif' WIDTH=22 HEIGHT=19 ALT=' cod_' TITLE='cod_'>";
  althtmldef "cod_" as "<U>cod</U>";
  latexdef "cod_" as "\underline{\rm cod}";
htmldef "id_" as
    "<IMG SRC='_idu.gif' WIDTH=12 HEIGHT=19 ALT=' id_' TITLE='id_'>";
  althtmldef "id_" as "<U>id</U>";
  latexdef "id_" as "\underline{\rm id}";
htmldef "o_" as "<IMG SRC='_ou.gif' WIDTH=7 HEIGHT=19 ALT=' o_' TITLE='o_'>";
  althtmldef "o_" as "<U>o</U>";
  latexdef "o_" as "\underline{\rm o}";
htmldef "Ded" as
    "<IMG SRC='_ded.gif' WIDTH=25 HEIGHT=19 ALT=' Ded' TITLE='Ded'>";
  althtmldef "Ded" as " Ded ";
  latexdef "Ded" as "{\rm Ded}";
htmldef "CatOLD" as
    " <IMG SRC='_cat.gif' WIDTH=24 HEIGHT=19 ALT=' Cat' TITLE='Cat'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'> ";
  althtmldef "CatOLD" as " Cat<SUB>OLD</SUB> ";
  latexdef "CatOLD" as "{\rm Cat_{OLD}}";
htmldef "hom" as
    "<IMG SRC='_hom.gif' WIDTH=27 HEIGHT=19 ALT=' hom' TITLE='hom'>";
  althtmldef "hom" as " hom ";
  latexdef "hom" as "{\rm hom}";
htmldef "Epic" as "Epic";
  althtmldef "Epic" as "Epic";
  latexdef "Epic" as "{\rm Epic}";
htmldef "MonoOLD" as " Mono<SUB>OLD</SUB> ";
  althtmldef "MonoOLD" as " Mono<SUB>OLD</SUB> ";
  latexdef "MonoOLD" as "{\rm Mono_{OLD}}";
htmldef "IsoOLD" as
    " <IMG SRC='_iso.gif' WIDTH=17 HEIGHT=19 ALT=' Iso' TITLE='Iso'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'> ";
  althtmldef "IsoOLD" as " Iso<SUB>OLD</SUB> ";
  latexdef "IsoOLD" as "{\rm Iso_{OLD}}";
htmldef "cinvOLD" as
    "<IMG SRC='_cinv.gif' WIDTH=27 HEIGHT=19 ALT=' cinv' TITLE='cinv'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "cinvOLD" as " cinv<SUB>OLD</SUB> ";
  latexdef "cinvOLD" as "{\rm cinv_{OLD}}";
/@ Duplicate removed by NM 17-Jul-2012 @/
/@ htmldef "id_" as "<U>id</U>";
  althtmldef "id_" as "<U>id</U>";
  latexdef "id_" as "\underline{\rm id}"; @/
htmldef "FuncOLD" as
    "<IMG SRC='_func.gif' WIDTH=32 HEIGHT=19 ALT=' Func' TITLE='Func'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "FuncOLD" as " Func<SUB>OLD</SUB> ";
  latexdef "FuncOLD" as "{\rm Func_{OLD}}";
htmldef "Isofunc" as
    " <IMG SRC='_isofunc.gif' WIDTH=45 HEIGHT=19 " +
    "ALT=' Isofunc' TITLE='Isofunc'> ";
  althtmldef "Isofunc" as " Isofunc ";
  latexdef "Isofunc" as "{\rm Isofunc}";
htmldef "SubCat" as
   " <IMG SRC='_subcat.gif' WIDTH=48 HEIGHT=19 ALT=' SubCat' TITLE='SubCat'> ";
  althtmldef "SubCat" as " SubCat ";
  latexdef "SubCat" as "{\rm SubCat}";
htmldef "InitObj" as
    " <IMG SRC='_initobj.gif' WIDTH=46 HEIGHT=19 " +
    "ALT=' InitObj' TITLE='InitObj'> ";
  althtmldef "InitObj" as " InitObj ";
  latexdef "InitObj" as "{\rm InitObj}";
htmldef "TermObj" as
    " <IMG SRC='_termobj.gif' WIDTH=56 HEIGHT=19 " +
    "ALT=' TermObj' TITLE='TermObj'> ";
  althtmldef "TermObj" as " TermObj ";
  latexdef "TermObj" as "{\rm TermObj}";
htmldef "Source" as
   " <IMG SRC='_source.gif' WIDTH=43 HEIGHT=19 ALT=' Source' TITLE='Source'> ";
  althtmldef "Source" as " Source ";
  latexdef "Source" as "{\rm Source}";
htmldef "Sink" as
    " <IMG SRC='_sink.gif' WIDTH=28 HEIGHT=19 ALT=' Sink' TITLE='Sink'> ";
  althtmldef "Sink" as " Sink ";
  latexdef "Sink" as "{\rm Sink}";
htmldef "Natural" as
    " <IMG SRC='_natural.gif' WIDTH=50 HEIGHT=19 " +
    "ALT=' Natural' TITLE='Natural'> ";
  althtmldef "Natural" as " Natural ";
  latexdef "Natural" as "{\rm Natural}";
htmldef "LimCat" as
   " <IMG SRC='_limcat.gif' WIDTH=49 HEIGHT=19 ALT=' LimCat' TITLE='LimCat'> ";
  althtmldef "LimCat" as " LimCat ";
  latexdef "LimCat" as "{\rm LimCat}";

htmldef "ProdObj" as " <IMG SRC='cdot.gif' " +
    "WIDTH=4 HEIGHT=19 ALT=' Prod' TITLE='Prod'>" +
    "<IMG SRC='_subobj.gif' WIDTH=18 HEIGHT=19 ALT=' Obj' TITLE='Obj'> ";
  althtmldef "ProdObj" as " ProdObj ";
  latexdef "ProdObj" as "\cdot_{\it obj}";
htmldef "SumObj" as " <IMG SRC='plus.gif' " +
    "WIDTH=13 HEIGHT=19 ALT=' Sum' TITLE='Sum'>" +
    "<IMG SRC='_subobj.gif' WIDTH=18 HEIGHT=19 ALT=' Obj' TITLE='Obj'> ";
  althtmldef "SumObj" as " +<SUB><I>Obj</I></SUB> ";
  latexdef "SumObj" as "+_{\it obj}";

htmldef "tar" as
    "<IMG SRC='_tar.gif' WIDTH=20 HEIGHT=19 ALT=' tar' TITLE='tar'>";
  althtmldef "tar" as "tar";
  latexdef "tar" as "{\rm tar}";
htmldef "tr" as "<IMG SRC='_tr.gif' WIDTH=12 HEIGHT=19 ALT=' tr' TITLE='tr'>";
  althtmldef "tr" as "tr";
  latexdef "tr" as "{\rm tr}";
htmldef ".Morphism" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.Morphism </I></SPAN>';
  althtmldef ".Morphism" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.Morphism </I></SPAN>';
  latexdef ".Morphism" as ".Morphism";
htmldef ".Object" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.Object </I></SPAN>';
  althtmldef ".Object" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.Object </I></SPAN>';
  latexdef ".Object" as ".Object";
htmldef ".graph" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.graph </I></SPAN>';
  althtmldef ".graph" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.graph </I></SPAN>';
  latexdef ".graph" as ".graph";
htmldef ".dom" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.dom </I></SPAN>';
  althtmldef ".dom" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.dom </I></SPAN>';
  latexdef ".dom" as ".dom";
htmldef ".cod" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.cod </I></SPAN>';
  althtmldef ".cod" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.cod </I></SPAN>';
  latexdef ".cod" as ".cod";
htmldef ".id" as '<SPAN CLASS=class STYLE="color:#C3C"><I>.id </I></SPAN>';
  althtmldef ".id" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>.id </I></SPAN>';
  latexdef ".id" as ".id";

htmldef "MorphismSetCat" as
    "<IMG SRC='_morphism.gif' WIDTH=63 HEIGHT=19 " +
    "ALT=' Morphism' TITLE='Morphism'>" +
    "<IMG SRC='_subsetcat.gif' WIDTH=34 HEIGHT=19 " +
    "ALT=' SetCat' TITLE='SetCat'>";
  althtmldef "MorphismSetCat" as "Morphism<SUB>SetCat</SUB>";
  latexdef "MorphismSetCat" as "Morphism_{\rm SetCat}";
htmldef "domSetCat" as
    "<IMG SRC='_dom.gif' WIDTH=26 HEIGHT=19 ALT=' dom' TITLE='dom'>" +
    "<IMG SRC='_subsetcat.gif' WIDTH=34 HEIGHT=19 " +
    "ALT=' SetCat' TITLE='SetCat'>";
  althtmldef "domSetCat" as "dom<SUB>SetCat</SUB>";
  latexdef "domSetCat" as "dom_{\rm SetCat}";
htmldef "graphSetCat" as
  "<IMG SRC='_graph.gif' WIDTH=38 HEIGHT=19 ALT=' graph' TITLE='graph'>" +
  "<IMG SRC='_subsetcat.gif' WIDTH=34 HEIGHT=19 ALT=' SetCat' TITLE='SetCat'>";
  althtmldef "graphSetCat" as "graph<SUB>SetCat</SUB>";
  latexdef "graphSetCat" as "graph_{\rm SetCat}";
htmldef "codSetCat" as "<IMG SRC='_cod.gif' WIDTH=22 HEIGHT=19 " +
    "ALT=' cod' TITLE='cod'><IMG SRC='_subsetcat.gif' WIDTH=34 HEIGHT=19 " +
    "ALT=' SetCat' TITLE='SetCat'>";
  althtmldef "codSetCat" as "cod<SUB>SetCat</SUB>";
  latexdef "codSetCat" as "cod_{\rm SetCat}";
htmldef "IdSetCat" as
    "<IMG SRC='_id.gif' WIDTH=12 HEIGHT=19 ALT=' Id' TITLE='Id'>" +
    "<IMG SRC='_subsetcat.gif' WIDTH=34 HEIGHT=19 " +
    "ALT=' SetCat' TITLE='SetCat'>";
  althtmldef "IdSetCat" as "Id<SUB>SetCat</SUB>";
  latexdef "IdSetCat" as "Id_{\rm SetCat}";
htmldef "roSetCat" as
    "<IMG SRC='_ro.gif' WIDTH=13 HEIGHT=19 ALT=' ro' TITLE='ro'>" +
    "<IMG SRC='_subsetcat.gif' WIDTH=34 HEIGHT=19 " +
    "ALT=' SetCat' TITLE='SetCat'>";
  althtmldef "roSetCat" as "ro<SUB>SetCat</SUB>";
  latexdef "roSetCat" as "ro_{\rm SetCat}";
htmldef "SetCatOLD" as
    "<IMG SRC='_setcat.gif' WIDTH=45 HEIGHT=19 ALT=' SetCat' TITLE='SetCat'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "SetCatOLD" as "SetCat<SUB>OLD</SUB>";
  latexdef "SetCatOLD" as "{\rm SetCat_{OLD}}";
htmldef "line" as
    "<IMG SRC='_line.gif' WIDTH=23 HEIGHT=19 ALT=' line' TITLE='line'>";
  althtmldef "line" as "line";
  latexdef "line" as "{\rm line}";
htmldef "seg" as
    "<IMG SRC='_seg.gif' WIDTH=21 HEIGHT=19 ALT=' seg' TITLE='seg'>";
  althtmldef "seg" as "seg";
  latexdef "seg" as "{\rm seg}";
htmldef "Kleene" as
    "<IMG SRC='_kleene.gif' WIDTH=43 HEIGHT=19 ALT=' Kleene' TITLE='Kleene'>";
  althtmldef "Kleene" as "Kleene";
  latexdef "Kleene" as "{\rm Kleene}";
htmldef "Words" as
    " <IMG SRC='_words.gif' WIDTH=40 HEIGHT=19 ALT=' Words' TITLE='Words'> ";
  althtmldef "Words" as " Words ";
  latexdef "Words" as "{\rm Words}";
htmldef "IndCls" as
   " <IMG SRC='_indcls.gif' WIDTH=40 HEIGHT=19 ALT=' IndCls' TITLE='IndCls'> ";
  althtmldef "IndCls" as " IndCls ";
  latexdef "IndCls" as "{\rm IndCls}";
/@
htmldef "IndClsBu" as
    "<IMG SRC='_indclsbu.gif' WIDTH=57 HEIGHT=19 " +
    "ALT=' IndClsBu' TITLE='IndClsBu'>";
  althtmldef "IndClsBu" as "IndClsBu";
  latexdef "IndClsBu" as "{\rm IndClsBu}";
@/
htmldef "Grammar" as
    "<IMG SRC='_grammar.gif' WIDTH=63 HEIGHT=19 " +
    "ALT=' Grammar' TITLE='Grammar'>";
  althtmldef "Grammar" as "Grammar";
  latexdef "Grammar" as "{\rm Grammar}";
htmldef "sym" as
    "<IMG SRC='_sym.gif' WIDTH=26 HEIGHT=19 ALT=' sym' TITLE='sym'>";
  althtmldef "sym" as "sym";
  latexdef "sym" as "{\rm sym}";
htmldef "prdct" as
    "<IMG SRC='_prdct.gif' WIDTH=35 HEIGHT=19 ALT=' prdct' TITLE='prdct'>";
  althtmldef "prdct" as "prdct";
  latexdef "prdct" as "{\rm prdct}";
htmldef "conc" as
    " <IMG SRC='_conc.gif' WIDTH=29 HEIGHT=19 ALT=' conc' TITLE='conc'> ";
  althtmldef "conc" as " conc ";
  latexdef "conc" as "{\rm conc}";
htmldef "-.c" as
    " <IMG SRC='lnot.gif' WIDTH=10 HEIGHT=19 ALT=' -.' TITLE='-.'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "-.c" as "&not;<SUB>&#x1D450;</SUB>";
  latexdef "-.c" as "-._{c}";
htmldef "/\c" as
    " <IMG SRC='wedge.gif' WIDTH=11 HEIGHT=19 ALT=' /\' TITLE='/\'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "/\c" as " /\<SUB>&#x1D450;</SUB> ";
  latexdef "/\c" as "\wedge_{c}";
htmldef "\/c" as
    " <IMG SRC='vee.gif' WIDTH=11 HEIGHT=19 ALT=' \/' TITLE='\/'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "\/c" as " \/<SUB>&#x1D450;</SUB> ";
  latexdef "\/c" as "\vee_{c}";
htmldef "=>c" as
    " <IMG SRC='to.gif' WIDTH=15 HEIGHT=19 ALT=' =&gt;' TITLE='=&gt;'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "=>c" as " &rarr;<SUB>&#x1D450;</SUB> ";
  latexdef "=>c" as "\rightarrow_{c}";
htmldef "<=>c" as
    " <IMG SRC='leftrightarrow.gif' WIDTH=15 HEIGHT=19 ALT=' &lt;=&gt;' " +
    "TITLE='&lt;=&gt;'><IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 " +
    "ALT=' c' TITLE='c'>";
  althtmldef "<=>c" as " &harr;<SUB>&#x1D450;</SUB> ";
  latexdef "<=>c" as "\leftrightarrow_{c}";
htmldef "_|_c" as
    "<IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT=' _|_' TITLE='_|_'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "_|_c" as
    "&#8869;<SUB>&#x1D450;</SUB>";
    /@ 2-Jan-2016 reverted sans-serif @/
  latexdef "_|_c" as "\perp_c";
htmldef "phc" as
    "<IMG SRC='_ph.gif' WIDTH=16 HEIGHT=19 ALT=' ph' TITLE='ph'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "phc" as "ph<SUB>&#x1D450;</SUB>";
  latexdef "phc" as "{\rm ph}_c";
htmldef "psc" as
    "<IMG SRC='_ps.gif' WIDTH=14 HEIGHT=19 ALT=' ps' TITLE='ps'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "psc" as "ps<SUB>&#x1D450;</SUB>";
  latexdef "psc" as "{\rm ps}_c";
htmldef "Pc" as
    "<IMG SRC='rmcp.gif' WIDTH=9 HEIGHT=19 ALT=' P' TITLE='P'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "Pc" as "P<SUB>&#x1D450;</SUB>";
  latexdef "Pc" as "{\rm P}_c";
htmldef "notc" as
    "<IMG SRC='_not.gif' WIDTH=21 HEIGHT=19 ALT=' not' TITLE='not'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "notc" as "not<SUB>&#x1D450;</SUB>";
  latexdef "notc" as "{\rm not}_c";
htmldef "andc" as
    "<IMG SRC='_and.gif' WIDTH=24 HEIGHT=19 ALT=' and' TITLE='and'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "andc" as "and<SUB>&#x1D450;</SUB>";
  latexdef "andc" as "{\rm and}_c";
htmldef "ors" as
    "<IMG SRC='__or.gif' WIDTH=13 HEIGHT=19 ALT=' or' TITLE='or'>" +
    "<IMG SRC='subs.gif' WIDTH=6 HEIGHT=19 ALT=' s' TITLE='s'>";
  althtmldef "ors" as "or<SUB>&#x1D460;</SUB>";
  latexdef "ors" as "{\rm or}_c";
htmldef "impc" as
    "<IMG SRC='_imp.gif' WIDTH=24 HEIGHT=19 ALT=' imp' TITLE='imp'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "impc" as "imp<SUB>&#x1D450;</SUB>";
  latexdef "impc" as "{\rm imp}_c";
htmldef "bic" as
    "<IMG SRC='_bi.gif' WIDTH=12 HEIGHT=19 ALT=' bi' TITLE='bi'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "bic" as "bi<SUB>&#x1D450;</SUB>";
  latexdef "bic" as "{\rm bi}_c";
htmldef "Prop" as
    "<IMG SRC='_prop.gif' WIDTH=30 HEIGHT=19 ALT=' Prop' TITLE='Prop'>";
  althtmldef "Prop" as "Prop";
  latexdef "Prop" as "{\rm Prop}";
htmldef "derv" as
    "<IMG SRC='_derv.gif' WIDTH=29 HEIGHT=19 ALT=' derv' TITLE='derv'>";
  althtmldef "derv" as "derv";
  latexdef "derv" as "{\rm derv}";
htmldef "PPoints" as "PPoints";
  althtmldef "PPoints" as "PPoints";
  latexdef "PPoints" as "{\rm PPoints}";
htmldef "PLines" as "PLines";
  althtmldef "PLines" as "PLines";
  latexdef "PLines" as "{\rm PLines}";
htmldef "Ig" as "Ig";
  althtmldef "Ig" as "Ig";
  latexdef "Ig" as "{\rm Ig}";
htmldef "coln" as "coln";
  althtmldef "coln" as "coln";
  latexdef "coln" as "{\rm coln}";
htmldef "con" as "con";
  althtmldef "con" as "con";
  latexdef "con" as "{\rm con}";
/@
htmldef "||g" as "||g";
  althtmldef "||g" as "||g";
  latexdef "||g" as "{\rm ||g}";
@/
htmldef "Ibg" as "Ibg";
  althtmldef "Ibg" as "Ibg";
  latexdef "Ibg" as "{\rm Ibg}";
htmldef "btw" as "btw";
  althtmldef "btw" as "btw";
  latexdef "btw" as "{\rm btw}";
htmldef "Segments" as "Segments";
  althtmldef "Segments" as "Segments";
  latexdef "Segments" as "{\rm Segments}";
htmldef "ray" as "ray";
  althtmldef "ray" as "ray";
  latexdef "ray" as "{\rm ray}";
htmldef "convex" as "convex";
  althtmldef "convex" as "convex";
  latexdef "convex" as "{\rm convex}";
htmldef "Ibcg" as "Ibcg";
  althtmldef "Ibcg" as "Ibcg";
  latexdef "Ibcg" as "{\rm Ibcg}";
htmldef "angc" as "angc";
  althtmldef "angc" as "angc";
  latexdef "angc" as "{\rm angc}";
htmldef "segc" as "segc";
  althtmldef "segc" as "segc";
  latexdef "segc" as "{\rm segc}";
htmldef "slices" as "slices";
  althtmldef "slices" as "slices";
  latexdef "slices" as "{\rm slices}";
htmldef "Cut" as "Cut";
  althtmldef "Cut" as "Cut";
  latexdef "Cut" as "{\rm Cut}";
htmldef "Neug" as "Neug";
  althtmldef "Neug" as "Neug";
  latexdef "Neug" as "{\rm Neug}";
htmldef "Circle" as "Circle";
  althtmldef "Circle" as "Circle";
  latexdef "Circle" as "{\rm Circle}";
htmldef "angle" as "angle";
  althtmldef "angle" as "angle";
  latexdef "angle" as "{\rm angle}";
htmldef "triangle" as "triangle";
  althtmldef "triangle" as "triangle";
  latexdef "triangle" as "{\rm triangle}";
htmldef "dWords" as "dWords";
  althtmldef "dWords" as "dWords";
  latexdef "dWords" as "{\rm dWords}";
htmldef "ss" as "ss";
  althtmldef "ss" as "ss";
  latexdef "ss" as "{\rm ss}";
htmldef "trcng" as "trcng";
  althtmldef "trcng" as "trcng";
  latexdef "trcng" as "{\rm trcng}";
htmldef "Halfplane" as "Halfplane";
  althtmldef "Halfplane" as "Halfplane";
  latexdef "Halfplane" as "{\rm Halfplane}";
htmldef "angtrg" as "angtrg";
  althtmldef "angtrg" as "angtrg";
  latexdef "angtrg" as "{\rm angtrg}";
htmldef "segtrg" as "segtrg";
  althtmldef "segtrg" as "segtrg";
  latexdef "segtrg" as "{\rm segtrg}";
htmldef ".~s" as
    " <IMG SRC='_.sim.gif' WIDTH=13 HEIGHT=19 ALT=' .~' TITLE='.~'> " +
    "<IMG SRC='subs.gif' WIDTH=6 HEIGHT=19 ALT=' s' TITLE='s'>";
  althtmldef ".~s" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>~<SUB>s</SUB> </I></SPAN>';
  latexdef ".~s" as "\sim_s";
htmldef ".~a" as
    " <IMG SRC='_.sim.gif' WIDTH=13 HEIGHT=19 ALT=' .~' TITLE='.~'> " +
    "<IMG SRC='suba.gif' WIDTH=6 HEIGHT=19 ALT=' a' TITLE='a'>";
  althtmldef ".~a" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>~<SUB>a</SUB> </I></SPAN>';
  latexdef ".~a" as "\sim_a";
htmldef ".~t" as
    " <IMG SRC='_.sim.gif' WIDTH=13 HEIGHT=19 ALT=' .~' TITLE='.~'> " +
    "<IMG SRC='subt.gif' WIDTH=6 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef ".~t" as
    '<SPAN CLASS=class STYLE="color:#C3C"><I>~<SUB>t</SUB> </I></SPAN>';
  latexdef ".~t" as "\sim_t";
/@ End of mathbox of FL @/
******* end of commenting out due to removal of FL's mathbox ******/


/* Mathbox of Jeff Madsen */
htmldef "Fne" as
    "<IMG SRC='_fne.gif' WIDTH=24 HEIGHT=19 ALT=' Fne' TITLE='Fne'>";
  althtmldef "Fne" as "Fne";
  latexdef "Fne" as "{\rm Fne}";
htmldef "Ref" as
    "<IMG SRC='_ref.gif' WIDTH=23 HEIGHT=19 ALT=' Ref' TITLE='Ref'>";
  althtmldef "Ref" as "Ref";
  latexdef "Ref" as "{\rm Ref}";
htmldef "PtFin" as
    "<IMG SRC='_ptfin.gif' WIDTH=36 HEIGHT=19 ALT=' PtFin' TITLE='PtFin'>";
  althtmldef "PtFin" as "PtFin";
  latexdef "PtFin" as "{\rm PtFin}";
htmldef "LocFin" as
    "<IMG SRC='_locfin.gif' WIDTH=44 HEIGHT=19 ALT=' LocFin' TITLE='LocFin'>";
  althtmldef "LocFin" as "LocFin";
  latexdef "LocFin" as "{\rm LocFin}";
htmldef "TotBnd" as
    "<IMG SRC='_totbnd.gif' WIDTH=46 HEIGHT=19 ALT=' TotBnd' TITLE='TotBnd'>";
  althtmldef "TotBnd" as "TotBnd";
  latexdef "TotBnd" as "{\rm TotBnd}";
htmldef "Bnd" as
    "<IMG SRC='_bnd.gif' WIDTH=25 HEIGHT=19 ALT=' Bnd' TITLE='Bnd'>";
  althtmldef "Bnd" as "Bnd";
  latexdef "Bnd" as "{\rm Bnd}";
htmldef "Ismty" as
    " <IMG SRC='_ismty.gif' WIDTH=36 HEIGHT=19 ALT=' Ismty' TITLE='Ismty'> ";
  althtmldef "Ismty" as " Ismty ";
  latexdef "Ismty" as "{\rm Ismty}";
htmldef "Rn" as
    "<IMG SRC='_bbrn.gif' WIDTH=19 HEIGHT=19 ALT=' Rn' TITLE='Rn'>";
  althtmldef "Rn" as "&#8477;<I><SUP>n</SUP></I>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Rn" as "\mathbb{R}^n";
htmldef "RngHom" as
   " <IMG SRC='_rnghom.gif' WIDTH=55 HEIGHT=19 ALT=' RngHom' TITLE='RngHom'> ";
  althtmldef "RngHom" as " RngHom ";
  latexdef "RngHom" as "{\rm RngHom}";
htmldef "RngIso" as
   " <IMG SRC='_rngiso.gif' WIDTH=43 HEIGHT=19 ALT=' RngIso' TITLE='RngIso'> ";
  althtmldef "RngIso" as " RngIso ";
  latexdef "RngIso" as "{\rm RngIso}";
htmldef "~=r" as
    " <IMG SRC='_simeqr.gif' WIDTH=18 HEIGHT=19 ALT=' ~=r' TITLE='~=r'> ";
  althtmldef "~=r" as " &#8771;<SUB>&#x1D45F;</SUB> ";
  latexdef "~=r" as "\simeq_r";
htmldef "CRingOps" as "CRingOps";
  althtmldef "CRingOps" as "CRingOps";
  latexdef "CRingOps" as "{\rm CRingOps}";
htmldef "Idl" as
    "<IMG SRC='_idl.gif' WIDTH=16 HEIGHT=19 ALT=' Idl' TITLE='Idl'>";
  althtmldef "Idl" as "Idl";
  latexdef "Idl" as "{\rm Idl}";
htmldef "PrIdl" as
    "<IMG SRC='_pridl.gif' WIDTH=31 HEIGHT=19 ALT=' PrIdl' TITLE='PrIdl'>";
  althtmldef "PrIdl" as "PrIdl";
  latexdef "PrIdl" as "{\rm PrIdl}";
htmldef "MaxIdl" as
    "<IMG SRC='_maxidl.gif' WIDTH=44 HEIGHT=19 ALT=' MaxIdl' TITLE='MaxIdl'>";
  althtmldef "MaxIdl" as "MaxIdl";
  latexdef "MaxIdl" as "{\rm MaxIdl}";
htmldef "PrRing" as
    "<IMG SRC='_prring.gif' WIDTH=45 HEIGHT=19 ALT=' PrRing' TITLE='PrRing'>";
  althtmldef "PrRing" as "PrRing";
  latexdef "PrRing" as "{\rm PrRing}";
htmldef "Dmn" as
    "<IMG SRC='_dmn.gif' WIDTH=30 HEIGHT=19 ALT=' Dmn' TITLE='Dmn'>";
  althtmldef "Dmn" as "Dmn";
  latexdef "Dmn" as "{\rm Dmn}";
htmldef "IdlGen" as
   " <IMG SRC='_idlgen.gif' WIDTH=42 HEIGHT=19 ALT=' IdlGen' TITLE='IdlGen'> ";
  althtmldef "IdlGen" as " IdlGen ";
  latexdef "IdlGen" as "{\rm IdlGen}";


/* Mathbox of Rodolfo Medina */
htmldef "Prt" as
    "<IMG SRC='_prt.gif' WIDTH=21 HEIGHT=19 ALT=' Prt' TITLE='Prt'> ";
  althtmldef "Prt" as "Prt ";
  latexdef "Prt" as "{\rm Prt}";

/* Mathbox of Stefan O'Rear */
htmldef "NoeACS" as "NoeACS";
  althtmldef "NoeACS" as "NoeACS";
  latexdef "NoeACS" as "\mathrm{NoeACS}";
htmldef "mzPolyCld" as "mzPolyCld";
  althtmldef "mzPolyCld" as "mzPolyCld";
  latexdef "mzPolyCld" as "{\rm mzPolyCld}";
htmldef "mzPoly" as "mzPoly";
  althtmldef "mzPoly" as "mzPoly";
  latexdef "mzPoly" as "{\rm mzPoly}";
htmldef "Dioph" as "Dioph";
  althtmldef "Dioph" as "Dioph";
  latexdef "Dioph" as "{\rm Dioph}";
htmldef "numer" as "numer";
  althtmldef "numer" as "numer";
  latexdef "numer" as "{\rm numer}";
htmldef "denom" as "denom";
  althtmldef "denom" as "denom";
  latexdef "denom" as "{\rm denom}";
htmldef "Pell1QR" as "Pell1QR";
  althtmldef "Pell1QR" as "Pell1QR";
  latexdef "Pell1QR" as "{\rm Pell1QR}";
htmldef "Pell14QR" as "Pell14QR";
  althtmldef "Pell14QR" as "Pell14QR";
  latexdef "Pell14QR" as "{\rm Pell14QR}";
htmldef "Pell1234QR" as "Pell1234QR";
  althtmldef "Pell1234QR" as "Pell1234QR";
  latexdef "Pell1234QR" as "{\rm Pell1234QR}";
htmldef "PellFund" as "PellFund";
  althtmldef "PellFund" as "PellFund";
  latexdef "PellFund" as "{\rm PellFund}";
htmldef "[]NN" as "&#x25FB;<SUB><I>NN</I></SUB>";
  althtmldef "[]NN" as "&#x25FB;<SUB><I>NN</I></SUB>";
  latexdef "[]NN" as "{\rm []NN}";
htmldef "rmX" as " X<SUB>rm</SUB> ";
  althtmldef "rmX" as " X<SUB>rm</SUB> ";
  latexdef "rmX" as "{\rm rmX}";
htmldef "rmY" as " Y<SUB>rm</SUB> ";
  althtmldef "rmY" as " Y<SUB>rm</SUB> ";
  latexdef "rmY" as "{\rm rmY}";
htmldef "LFinGen" as "LFinGen";
  althtmldef "LFinGen" as "LFinGen";
  latexdef "LFinGen" as "{\rm LFinGen}";
htmldef "LNoeM" as "LNoeM";
  althtmldef "LNoeM" as "LNoeM";
  latexdef "LNoeM" as "{\rm LNoeM}";
htmldef "(+)m" as " <IMG SRC='oplus.gif' WIDTH=13 HEIGHT=19 " +
    "ALT=' (+)' TITLE='(+)'><SUB>m</SUB> ";
  althtmldef "(+)m" as " &#x2295;<SUB>m</SUB> ";
  latexdef "(+)m" as "\oplus_{m}";
htmldef "freeLMod" as " freeLMod ";
  althtmldef "freeLMod" as " freeLMod ";
  latexdef "freeLMod" as "{\rm freeLMod}";
htmldef "unitVec" as " unitVec ";
  althtmldef "unitVec" as " unitVec ";
  latexdef "unitVec" as "{\rm unitVec}";
htmldef "LIndF" as " LIndF ";
  althtmldef "LIndF" as " LIndF ";
  latexdef "LIndF" as " {\rm LIndF} ";
htmldef "LIndS" as "LIndS";
  althtmldef "LIndS" as "LIndS";
  latexdef "LIndS" as "{\rm LIndS}";
htmldef "LNoeR" as "LNoeR";
  althtmldef "LNoeR" as "LNoeR";
  latexdef "LNoeR" as "{\rm LNoeR}";
htmldef "ldgIdlSeq" as "ldgIdlSeq";
  althtmldef "ldgIdlSeq" as "ldgIdlSeq";
  latexdef "ldgIdlSeq" as "\mathrm{ldgIdlSeq}";
htmldef "Monic" as
    " <IMG SRC='_monic.gif' WIDTH=38 HEIGHT=19 ALT=' Monic' TITLE='Monic'> ";
  althtmldef "Monic" as " Monic ";
  latexdef "Monic" as "{\rm Monic}";
htmldef "Poly<" as " Poly<sub>&lt;</sub> ";
  althtmldef "Poly<" as " Poly<sub>&lt;</sub> ";
  latexdef "Poly<" as "{\rm Poly<}";
htmldef "degAA" as "deg<SUB>AA</SUB>";
  althtmldef "degAA" as "deg<SUB>AA</SUB>";
  latexdef "degAA" as "{\rm degAA}";
htmldef "minPolyAA" as "minPolyAA";
  althtmldef "minPolyAA" as "minPolyAA";
  latexdef "minPolyAA" as "{\rm minPolyAA}";
htmldef "_ZZ" as "<SPAN STYLE='text-decoration: overline;'>&#8484;</SPAN>";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "_ZZ" as
                 "<SPAN STYLE='text-decoration: overline;'>&#8484;</SPAN>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "_ZZ" as "{\rm _ZZ}";
htmldef "IntgOver" as "IntgOver";
  althtmldef "IntgOver" as "IntgOver";
  latexdef "IntgOver" as "{\rm IntgOver}";
htmldef "pmTrsp" as "pmTrsp";
  althtmldef "pmTrsp" as "pmTrsp";
  latexdef "pmTrsp" as "\mathrm{pmTrsp}";
htmldef "pmSgn" as "pmSgn";
  althtmldef "pmSgn" as "pmSgn";
  latexdef "pmSgn" as "\mathrm{pmSgn}";
htmldef "maMul" as " maMul ";
  althtmldef "maMul" as " maMul ";
  latexdef "maMul" as " \mathrm{maMul} ";
htmldef "Mat" as " Mat ";
  althtmldef "Mat" as " Mat ";
  latexdef "Mat" as " \mathrm{Mat} ";
htmldef "maDet" as " maDet ";
  althtmldef "maDet" as " maDet ";
  latexdef "maDet" as " \mathrm{maDet} ";
htmldef "maAdju" as " maAdju ";
  althtmldef "maAdju" as " maAdju ";
  latexdef "maAdju" as " \mathrm{maAdju} ";
htmldef "MEndo" as "MEndo";
  althtmldef "MEndo" as "MEndo";
  latexdef "MEndo" as "\mathrm{MEndo}";
htmldef "SubDRing" as "SubDRing";
  althtmldef "SubDRing" as "SubDRing";
  latexdef "SubDRing" as "\mathrm{SubDRing}";
htmldef "Cntr" as "Cntr";
  althtmldef "Cntr" as "Cntr";
  latexdef "Cntr" as "\mathrm{Cntr}";
htmldef "Cntz" as "Cntz";
  althtmldef "Cntz" as "Cntz";
  latexdef "Cntz" as "\mathrm{Cntz}";
htmldef "CytP" as "CytP";
  althtmldef "CytP" as "CytP";
  latexdef "CytP" as "\mathrm{CytP}";
htmldef "TopSep" as "TopSep";
  althtmldef "TopSep" as "TopSep";
  latexdef "TopSep" as "{\rm TopSep}";
htmldef "TopLnd" as "TopLnd";
  althtmldef "TopLnd" as "TopLnd";
  latexdef "TopLnd" as "{\rm TopLnd}";
/* End of mathbox of Stefan O'Rear */


/* Mathbox of Steve Rodriguez */
/* End of mathbox of Steve Rodriguez */


/* Mathbox of Andrew Salmon */
/* geometry proposal */
htmldef "+r" as "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT=' r' TITLE='r'>";
  althtmldef "+r" as "+<SUB>&#x1D45F;</SUB>";
  latexdef "+r" as "+_r";
htmldef "-r" as
    "<IMG SRC='minus.gif' WIDTH=11 HEIGHT=19 ALT=' -' TITLE='-'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT=' r' TITLE='r'>";
  althtmldef "-r" as "-<SUB>&#x1D45F;</SUB>";
  latexdef "-r" as "-_r";
htmldef ".v" as "<IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' .' TITLE='.'>" +
    "<IMG SRC='subv.gif' WIDTH=6 HEIGHT=19 ALT=' v' TITLE='v'>";
  althtmldef ".v" as ".<SUB>&#x1D463;</SUB>";
  latexdef ".v" as "._v";
htmldef "PtDf" as
    "<IMG SRC='_ptdf.gif' WIDTH=31 HEIGHT=19 ALT=' PtDf' TITLE='PtDf'>";
  althtmldef "PtDf" as "PtDf";
  latexdef "PtDf" as "PtDf";
htmldef "RR3" as
    "<IMG SRC='bbr.gif' WIDTH=13 HEIGHT=19 ALT=' RR' TITLE='RR'>" +
    "<IMG SRC='sup3.gif' WIDTH=6 HEIGHT=19 ALT=' 3' TITLE='3'>";
  althtmldef "RR3" as "RR3";
  latexdef "RR3" as "RR3";
/*
htmldef "plane3" as
    "<IMG SRC='_plane.gif' WIDTH=35 HEIGHT=19 ALT=' plane' TITLE='plane'>" +
    "<IMG SRC='sup3.gif' WIDTH=6 HEIGHT=19 ALT=' 3' TITLE='3'>";
  althtmldef "plane3" as "plane3";
  latexdef "plane3" as "plane3";
*/
htmldef "line3" as
    "<IMG SRC='_line.gif' WIDTH=23 HEIGHT=19 ALT=' line' TITLE='line'>" +
    "<IMG SRC='sup3.gif' WIDTH=6 HEIGHT=19 ALT=' 3' TITLE='3'>";
  althtmldef "line3" as "line3";
  latexdef "line3" as "line3";

/* Mathbox of Jarvin Udandy */
htmldef "jph" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jph</I></SPAN>';
 althtmldef "jph" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jph</I></SPAN>';
 latexdef "jph" as "\rm{jph}";
htmldef "jps" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jps</I></SPAN>';
 althtmldef "jps" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jps</I></SPAN>';
 latexdef "jps" as "\rm{jps}";
htmldef "jch" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jch</I></SPAN>';
 althtmldef "jch" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jch</I></SPAN>';
 latexdef "jch" as "\rm{jch}";
htmldef "jth" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jth</I></SPAN>';
 althtmldef "jth" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jth</I></SPAN>';
 latexdef "jth" as "\rm{jth}";
htmldef "jta" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jta</I></SPAN>';
 althtmldef "jta" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jta</I></SPAN>';
 latexdef "jta" as "\rm{jta}";
htmldef "jet" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jet</I></SPAN>';
 althtmldef "jet" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jet</I></SPAN>';
 latexdef "jet" as "\rm{jet}";
htmldef "jze" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jze</I></SPAN>';
 althtmldef "jze" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jze</I></SPAN>';
 latexdef "jze" as "\rm{jze}";
htmldef "jsi" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jps</I></SPAN>';
 althtmldef "jsi" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jps</I></SPAN>';
 latexdef "jsi" as "\rm{jsi}";
htmldef "jrh" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jrh</I></SPAN>';
 althtmldef "jrh" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jrh</I></SPAN>';
 latexdef "jrh" as "\rm{jrh}";
htmldef "jmu" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jmu</I></SPAN>';
 althtmldef "jmu" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jmu</I></SPAN>';
 latexdef "jmu" as "\rm{jmu}";
htmldef "jla" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jla</I></SPAN>';
 althtmldef "jla" as
  '<SPAN CLASS=wff STYLE="color:blue"><I>jla</I></SPAN>';
 latexdef "jla" as "\rm{jla}";
/* End of Jarvin Udandy's mathbox */

/* Mathbox of Alexander van der Vekens */
htmldef "defAt" as ' defAt ';
 althtmldef "defAt" as ' defAt ';
 latexdef "defAt" as "{\rm defAt}";
htmldef "'''" as '&#39&#39&#39';
 althtmldef "'''" as '&#39&#39&#39';
 latexdef "'''" as "\textquoteright\textquoteright\textquoteright";
htmldef "((" as ' ((';
 althtmldef "((" as ' ((';
 latexdef "((" as " ((";
htmldef "))" as ')) ';
 althtmldef "))" as ')) ';
 latexdef "))" as ")) ";
htmldef "CyclShift" as ' CyclShift ';
 althtmldef "CyclShift" as ' CyclShift ';
 latexdef "CyclShift" as "{\rm CyclShift}";
htmldef "LastS" as ' LastS ';
 althtmldef "LastS" as ' LastS ';
 latexdef "LastS" as "{\rm LastS}";
htmldef "WWalks" as ' WWalks ';
 althtmldef "WWalks" as ' WWalks ';
 latexdef "WWalks" as "{\rm WWalks}";
htmldef "WWalksN" as ' WWalksN ';
 althtmldef "WWalksN" as ' WWalksN ';
 latexdef "WWalksN" as "{\rm WWalksN}";
htmldef "2WalksOt" as ' 2WalksOt ';
 althtmldef "2WalksOt" as ' 2WalksOt ';
 latexdef "2WalksOt" as "{\rm 2WalksOt}";
htmldef "2WalksOnOt" as ' 2WalksOnOt ';
 althtmldef "2WalksOnOt" as ' 2WalksOnOt ';
 latexdef "2WalksOnOt" as "{\rm 2WalksOnOt}";
htmldef "2SPathOnOt" as ' 2SPathOnOt ';
 althtmldef "2SPathOnOt" as ' 2SPathOnOt ';
 latexdef "2SPathOnOt" as "{\rm 2SPathOnOt}";
htmldef "2SPathsOt" as ' 2SPathOnOt ';
 althtmldef "2SPathsOt" as ' 2SPathsOt ';
 latexdef "2SPathsOt" as "{\rm 2SPathsOt}";
htmldef "RegUSGrph" as ' RegUSGrph ';
 althtmldef "RegUSGrph" as ' RegUSGrph ';
 latexdef "RegUSGrph" as "{\rm RegUSGrph}";
htmldef "RegGrph" as ' RegGrph ';
 althtmldef "RegGrph" as ' RegGrph ';
 latexdef "RegGrph" as "{\rm RegGrph}";
htmldef "FriendGrph" as ' FriendGrph ';
 althtmldef "FriendGrph" as ' FriendGrph ';
 latexdef "FriendGrph" as "{\rm FriendGrph}";
/* End of Alexander van der Vekens's mathbox */

/* Mathbox of David A. Wheeler */
htmldef ">_" as
    " <IMG SRC='ge.gif' WIDTH=11 HEIGHT=19 ALT=' &gt;_' TITLE='&gt;_'> ";
  althtmldef ">_" as ' &ge; ';
  latexdef ">_" as "\ge";
htmldef ">" as
    " <IMG SRC='gt.gif' WIDTH=11 HEIGHT=19 ALT=' &gt;' TITLE='&gt;'> ";
  althtmldef ">" as ' &gt; ';
  latexdef ">" as ">";
/*
htmldef "sinh" as
    "<IMG SRC='_sinh.gif' WIDTH=20 HEIGHT=19 ALT=' sinh' TITLE='sinh'>";
*/
htmldef "sinh" as "sinh";
  althtmldef "sinh" as "sinh";
  latexdef "sinh" as "\sinh";
/*
htmldef "cosh" as
    "<IMG SRC='_cosh.gif' WIDTH=20 HEIGHT=19 ALT=' cosh' TITLE='cosh'>";
*/
htmldef "cosh" as "cosh";
  althtmldef "cosh" as "cosh";
  latexdef "cosh" as "\cosh";
/*
htmldef "tanh" as
    "<IMG SRC='_tanh.gif' WIDTH=20 HEIGHT=19 ALT=' tanh' TITLE='tanh'>";
*/
htmldef "tanh" as "tanh";
  althtmldef "tanh" as "tanh";
  latexdef "tanh" as "\tanh";
htmldef "sec" as
    "<IMG SRC='_sec.gif' WIDTH=20 HEIGHT=19 ALT=' sec' TITLE='sec'>";
  althtmldef "sec" as "sec";
  latexdef "sec" as "\sec";
htmldef "csc" as
    "<IMG SRC='_csc.gif' WIDTH=20 HEIGHT=19 ALT=' csc' TITLE='csc'>";
  althtmldef "csc" as "csc";
  latexdef "csc" as "\csc";
htmldef "cot" as
    "<IMG SRC='_cot.gif' WIDTH=20 HEIGHT=19 ALT=' cot' TITLE='cot'>";
  althtmldef "cot" as "cot";
  latexdef "cot" as "\cot";
/*
htmldef "_" as
    "<IMG SRC='underscore.gif' WIDTH=20 HEIGHT=19 ALT=' _' TITLE='_'>";
*/
htmldef "_" as '<FONT COLOR="#808080">_</FONT>';
  althtmldef "_" as '<SPAN CLASS=hidden STYLE="color:gray">_</SPAN>';
  latexdef "_" as "\_";
htmldef "." as
    "<IMG SRC='period.gif' WIDTH=20 HEIGHT=19 ALT=' period' TITLE='period'>";
  althtmldef "." as ".";
  latexdef "." as "\.";
/*
htmldef "sgn" as
    "<IMG SRC='sgn.gif' WIDTH=20 HEIGHT=19 ALT=' sgn' TITLE='sgn'>";
*/
htmldef "sgn" as "sgn";
  althtmldef "sgn" as "sgn";
  latexdef "sgn" as "sgn";
/*
htmldef "ceiling" as
   "<IMG SRC='ceiling.gif' WIDTH=20 HEIGHT=19 ALT=' ceiling' TITLE='ceiling'>";
*/
htmldef "ceiling" as "&#8968;";
  althtmldef "ceiling" as "&#8968;";
  latexdef "ceiling" as "ceiling";
htmldef "logb" as "logb";
  althtmldef "logb" as "logb";
  latexdef "logb" as "logb";
htmldef "log_" as "log_";
  althtmldef "log_" as "log_";
  latexdef "log_" as "log_";

/* Mathbox of Alan Sare */
htmldef "(." as
    "<IMG SRC='period.gif' WIDTH=4 HEIGHT=19 ALT=' (.' TITLE='(.'>";
althtmldef "(." as
'<SPAN STYLE="color:#00CD00">&#40;&#160;&#160;&#160;</SPAN>';
/* This puts 0 white spaces before the left parenthesis(&#40) and 3 white
   spaces after. Here the parenthesis shall be colored bright green, the same
   color as the arrow. Here we are trying to use green parentheses instead of
   green periods. The reasoning is that parenthesis are better because its more
   consistent
   with a) conventional metamath notation so the User understands it better;
   b) Because these parentheses are now bright green, that sufficiently
   distinguishes these parentheses from the parentheses used to parse the
   wffs. The green parentheses are notation of the Virtual Deduction "mediator"
   notation. */
latexdef "(." as ".";
htmldef ")." as
    "<IMG SRC='period.gif' WIDTH=4 HEIGHT=19 ALT=' ).' TITLE=').'>";
althtmldef ")." as
'<SPAN STYLE="color:#00CD00">&#160;&#160;&#160;&#41;</SPAN>';
/* This puts 3 white spaces before the right parenthesis(&#41) and 0 white
   spaces after. Here the parenthesis shall be colored bright green, the same
   color as the arrow. Here we are trying to use green parentheses instead of
   green periods. The reasoning is that parenthesis are better because its more
   consistent
   with a) conventional metamath notation so the User understands it better;
   b) Because these parentheses are now bright green, that sufficiently
   distinguishes these parentheses from the parentheses used to parse the
   wffs. The green parentheses are notation of the Virtual Deduction "mediator"
   notation. */
latexdef ")." as ".";
htmldef "->." as " <IMG SRC='blacktriangleright.gif' " +
    "WIDTH=11 HEIGHT=19 ALT=' -&gt;.' TITLE='-&gt;.'> ";
althtmldef "->." as
  '<SPAN STYLE="color:#00CD00"><FONT FACE=veranda>' +
  '&#160;&#160;&#160;&#9654;&#160;&#160;&#160;</FONT></SPAN>';
/* This should work better than the one above because we put white spaces
   around the arrow. It is better with an equal number of white spaces on each
   side of the arrow. The bright green for the virtual deduction notation
   works well. */
latexdef "->." as "\blacktriangleright";
htmldef "->.." as " <IMG SRC='__tobold.gif' " +
    "WIDTH=15 HEIGHT=19 ALT=' -&gt;..' TITLE='-&gt;..'> ";
  althtmldef "->.." as " <B>&rarr;</B> ";
  latexdef "->.." as "\mbox{\boldmath $\rightarrow$}}";
htmldef ",." as
    "<IMG SRC='comma.gif' WIDTH=4 HEIGHT=19 ALT=' ,.' TITLE=',.'>";
althtmldef ",." as
    '<SPAN STYLE="color:#00CD00"><FONT SIZE=4>' +
    '&#160;&#160;&#160;&#44;&#160;&#160;&#160;</FONT></SPAN>';
/* This color is green3. It is brighter and lighter than Irish flag. It is
   bright enough to stand out and it is not too light
   to be seen. It is clearly distinguishable from black. */
latexdef ",." as " , ";
/* End of Alan Sare's mathbox */


/* Mathbox of Jonathan Ben-Naim */
htmldef "ph'" as "<IMG SRC='_bnj_phiPrime.gif'   WIDTH=15 HEIGHT=19" +
       " ALT=" + '"' + " ph'" + '"' + " TITLE=" + '"' + "ph'" + '"' + ">";
htmldef "ps'" as "<IMG SRC='_bnj_psiPrime.gif'   WIDTH=16 HEIGHT=19" +
       " ALT=" + '"' + " ps'" + '"' + " TITLE=" + '"' + "ps'" + '"' + ">";
htmldef "ch'" as "<IMG SRC='_bnj_chiPrime.gif'   WIDTH=16 HEIGHT=19" +
       " ALT=" + '"' + " ch'" + '"' + " TITLE=" + '"' + "ch'" + '"' + ">";
htmldef "th'" as "<IMG SRC='_bnj_thetaPrime.gif' WIDTH=12 HEIGHT=19" +
       " ALT=" + '"' + " th'" + '"' + " TITLE=" + '"' + "th'" + '"' + ">";
htmldef "ta'" as "<IMG SRC='_bnj_tauPrime.gif'   WIDTH=14 HEIGHT=19" +
       " ALT=" + '"' + " ta'" + '"' + " TITLE=" + '"' + "ta'" + '"' + ">";
htmldef "et'" as "<IMG SRC='_bnj_etaPrime.gif'   WIDTH=13 HEIGHT=19" +
       " ALT=" + '"' + " et'" + '"' + " TITLE=" + '"' + "et'" + '"' + ">";
htmldef "ze'" as "<IMG SRC='_bnj_zetaPrime.gif'  WIDTH=13 HEIGHT=19" +
       " ALT=" + '"' + " ze'" + '"' + " TITLE=" + '"' + "ze'" + '"' + ">";
htmldef "si'" as "<IMG SRC='_bnj_sigmaPrime.gif' WIDTH=14 HEIGHT=19" +
       " ALT=" + '"' + " si'" + '"' + " TITLE=" + '"' + "si'" + '"' + ">";
htmldef "rh'" as "<IMG SRC='_bnj_rhoPrime.gif'   WIDTH=13 HEIGHT=19" +
       " ALT=" + '"' + " rh'" + '"' + " TITLE=" + '"' + "rh'" + '"' + ">";
althtmldef "ph'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;&prime;</SPAN>';
althtmldef "ps'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;&prime;</SPAN>';
althtmldef "ch'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;&prime;</SPAN>';
althtmldef "th'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;&prime;</SPAN>';
althtmldef "ta'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;&prime;</SPAN>';
althtmldef "et'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;&prime;</SPAN>';
althtmldef "ze'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;&prime;</SPAN>';
althtmldef "si'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;&prime;</SPAN>';
althtmldef "rh'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;&prime;</SPAN>';
latexdef "ph'" as "\varphi'";
latexdef "ps'" as "\psi'";
latexdef "ch'" as "\chi'";
latexdef "th'" as "\theta'";
latexdef "ta'" as "\tau'";
latexdef "et'" as "\eta'";
latexdef "ze'" as "\zeta'";
latexdef "si'" as "\sigma'";
latexdef "rh'" as "\rho'";
htmldef 'ph"' as "<IMG SRC='_bnj_phiPrimePrime.gif'   WIDTH=18 HEIGHT=19" +
      " ALT=' ph" + '"' + "' TITLE='ph" + '"' + "'>";
htmldef 'ps"' as "<IMG SRC='_bnj_psiPrimePrime.gif'   WIDTH=19 HEIGHT=19" +
      " ALT=' ps" + '"' + "' TITLE='ps" + '"' + "'>";
htmldef 'ch"' as "<IMG SRC='_bnj_chiPrimePrime.gif'   WIDTH=19 HEIGHT=19" +
      " ALT=' ch" + '"' + "' TITLE='ch" + '"' + "'>";
htmldef 'th"' as "<IMG SRC='_bnj_thetaPrimePrime.gif' WIDTH=15 HEIGHT=19" +
      " ALT=' th" + '"' + "' TITLE='th" + '"' + "'>";
htmldef 'ta"' as "<IMG SRC='_bnj_tauPrimePrime.gif'   WIDTH=17 HEIGHT=19" +
      " ALT=' ta" + '"' + "' TITLE='ta" + '"' + "'>";
htmldef 'et"' as "<IMG SRC='_bnj_etaPrimePrime.gif'   WIDTH=16 HEIGHT=19" +
      " ALT=' et" + '"' + "' TITLE='et" + '"' + "'>";
htmldef 'ze"' as "<IMG SRC='_bnj_zetaPrimePrime.gif'  WIDTH=16 HEIGHT=19" +
      " ALT=' ze" + '"' + "' TITLE='ze" + '"' + "'>";
htmldef 'si"' as "<IMG SRC='_bnj_sigmaPrimePrime.gif' WIDTH=17 HEIGHT=19" +
      " ALT=' si" + '"' + "' TITLE='si" + '"' + "'>";
htmldef 'rh"' as "<IMG SRC='_bnj_rhoPrimePrime.gif'   WIDTH=16 HEIGHT=19" +
      " ALT=' rh" + '"' + "' TITLE='rh" + '"' + "'>";
althtmldef 'ph"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;&Prime;</SPAN>';
althtmldef 'ps"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;&Prime;</SPAN>';
althtmldef 'ch"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;&Prime;</SPAN>';
althtmldef 'th"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;&Prime;</SPAN>';
althtmldef 'ta"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;&Prime;</SPAN>';
althtmldef 'et"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;&Prime;</SPAN>';
althtmldef 'ze"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;&Prime;</SPAN>';
althtmldef 'si"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;&Prime;</SPAN>';
althtmldef 'rh"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;&Prime;</SPAN>';
latexdef 'ph"' as "\varphi''";
latexdef 'ps"' as "\psi''";
latexdef 'ch"' as "\chi''";
latexdef 'th"' as "\theta''";
latexdef 'ta"' as "\tau''";
latexdef 'et"' as "\eta''";
latexdef 'ze"' as "\zeta''";
latexdef 'si"' as "\sigma''";
latexdef 'rh"' as "\rho''";
htmldef "ph0"  as "<IMG SRC='_bnj_phi0.gif'   WIDTH=18 HEIGHT=19" +
    " ALT=' ph0' TITLE='ph0'>";
htmldef "ps0"  as "<IMG SRC='_bnj_psi0.gif'   WIDTH=19 HEIGHT=19" +
    " ALT=' ps0' TITLE='ps0'>";
htmldef "ch0_" as "<IMG SRC='_bnj_chi0.gif'   WIDTH=19 HEIGHT=19" +
    " ALT=' ch0_' TITLE='ch0_'>";
htmldef "th0"  as "<IMG SRC='_bnj_theta0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' th0' TITLE='th0'>";
htmldef "ta0"  as "<IMG SRC='_bnj_tau0.gif'   WIDTH=17 HEIGHT=19" +
    " ALT=' ta0' TITLE='ta0'>";
htmldef "et0"  as "<IMG SRC='_bnj_eta0.gif'   WIDTH=16 HEIGHT=19" +
    " ALT=' et0' TITLE='et0'>";
htmldef "ze0"  as "<IMG SRC='_bnj_zeta0.gif'  WIDTH=16 HEIGHT=19" +
    " ALT=' ze0' TITLE='ze0'>";
htmldef "si0"  as "<IMG SRC='_bnj_sigma0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' si0' TITLE='si0'>";
htmldef "rh0"  as "<IMG SRC='_bnj_rho0.gif'   WIDTH=16 HEIGHT=19" +
    " ALT=' rh0' TITLE='rh0'>";
althtmldef "ph0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;<SUB>0</SUB></SPAN>';
althtmldef "ps0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;<SUB>0</SUB></SPAN>';
althtmldef "ch0_" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;<SUB>0</SUB></SPAN>';
althtmldef "th0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;<SUB>0</SUB></SPAN>';
althtmldef "ta0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;<SUB>0</SUB></SPAN>';
althtmldef "et0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;<SUB>0</SUB></SPAN>';
althtmldef "ze0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;<SUB>0</SUB></SPAN>';
althtmldef "si0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;<SUB>0</SUB></SPAN>';
althtmldef "rh0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;<SUB>0</SUB></SPAN>';
latexdef "ph0"  as "\varphi_0";
latexdef "ps0"  as "\psi_0";
latexdef "ch0_" as "\chi_0";
latexdef "th0"  as "\theta_0";
latexdef "ta0"  as "\tau_0";
latexdef "et0"  as "\eta_0";
latexdef "ze0"  as "\zeta_0";
latexdef "si0"  as "\sigma_0";
latexdef "rh0"  as "\rho_0";
htmldef "ph1" as "<IMG SRC='_bnj_phi1.gif'   WIDTH=16 HEIGHT=19" +
    " ALT=' ph1' TITLE='ph1'>";
htmldef "ps1" as "<IMG SRC='_bnj_psi1.gif'   WIDTH=17 HEIGHT=19" +
    " ALT=' ps1' TITLE='ps1'>";
htmldef "ch1" as "<IMG SRC='_bnj_chi1.gif'   WIDTH=17 HEIGHT=19" +
    " ALT=' ch1' TITLE='ch1'>";
htmldef "th1" as "<IMG SRC='_bnj_theta1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' th1' TITLE='th1'>";
htmldef "ta1" as "<IMG SRC='_bnj_tau1.gif'   WIDTH=15 HEIGHT=19" +
    " ALT=' ta1' TITLE='ta1'>";
htmldef "et1" as "<IMG SRC='_bnj_eta1.gif'   WIDTH=14 HEIGHT=19" +
    " ALT=' et1' TITLE='et1'>";
htmldef "ze1" as "<IMG SRC='_bnj_zeta1.gif'  WIDTH=14 HEIGHT=19" +
    " ALT=' ze1' TITLE='ze1'>";
htmldef "si1" as "<IMG SRC='_bnj_sigma1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' si1' TITLE='si1'>";
htmldef "rh1" as "<IMG SRC='_bnj_rho1.gif'   WIDTH=14 HEIGHT=19" +
    " ALT=' rh1' TITLE='rh1'>";
althtmldef "ph1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;<SUB>1</SUB></SPAN>';
althtmldef "ps1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;<SUB>1</SUB></SPAN>';
althtmldef "ch1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;<SUB>1</SUB></SPAN>';
althtmldef "th1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;<SUB>1</SUB></SPAN>';
althtmldef "ta1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;<SUB>1</SUB></SPAN>';
althtmldef "et1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;<SUB>1</SUB></SPAN>';
althtmldef "ze1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;<SUB>1</SUB></SPAN>';
althtmldef "si1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;<SUB>1</SUB></SPAN>';
althtmldef "rh1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;<SUB>1</SUB></SPAN>';
latexdef "ph1" as "\varphi_1";
latexdef "ps1" as "\psi_1";
latexdef "ch1" as "\chi_1";
latexdef "th1" as "\theta_1";
latexdef "ta1" as "\tau_1";
latexdef "et1" as "\eta_1";
latexdef "ze1" as "\zeta_1";
latexdef "si1" as "\sigma_1";
latexdef "rh1" as "\rho_1";
htmldef "a'" as "<IMG SRC='_bnj_aPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " a'" + '"' + " TITLE=" + '"' + "a'" + '"' + ">";
htmldef "b'" as "<IMG SRC='_bnj_bPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " b'" + '"' + " TITLE=" + '"' + "b'" + '"' + ">";
htmldef "c'" as "<IMG SRC='_bnj_cPrime.gif' WIDTH=11 HEIGHT=19" +
    " ALT=" + '"' + " c'" + '"' + " TITLE=" + '"' + "c'" + '"' + ">";
htmldef "d'" as "<IMG SRC='_bnj_dPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " d'" + '"' + " TITLE=" + '"' + "d'" + '"' + ">";
htmldef "e'" as "<IMG SRC='_bnj_ePrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " e'" + '"' + " TITLE=" + '"' + "e'" + '"' + ">";
htmldef "f'" as "<IMG SRC='_bnj_fPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " f'" + '"' + " TITLE=" + '"' + "f'" + '"' + ">";
htmldef "g'" as "<IMG SRC='_bnj_gPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " g'" + '"' + " TITLE=" + '"' + "g'" + '"' + ">";
htmldef "h'" as "<IMG SRC='_bnj_hPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " h'" + '"' + " TITLE=" + '"' + "h'" + '"' + ">";
htmldef "i'" as "<IMG SRC='_bnj_iPrime.gif' WIDTH=10 HEIGHT=19" +
    " ALT=" + '"' + " i'" + '"' + " TITLE=" + '"' + "i'" + '"' + ">";
htmldef "j'" as "<IMG SRC='_bnj_jPrime.gif' WIDTH=11 HEIGHT=19" +
    " ALT=" + '"' + " j'" + '"' + " TITLE=" + '"' + "j'" + '"' + ">";
htmldef "k'" as "<IMG SRC='_bnj_kPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " k'" + '"' + " TITLE=" + '"' + "k'" + '"' + ">";
htmldef "l'" as "<IMG SRC='_bnj_lPrime.gif' WIDTH=9  HEIGHT=19" +
    " ALT=" + '"' + " l'" + '"' + " TITLE=" + '"' + "l'" + '"' + ">";
htmldef "m'" as "<IMG SRC='_bnj_mPrime.gif' WIDTH=18 HEIGHT=19" +
    " ALT=" + '"' + " m'" + '"' + " TITLE=" + '"' + "m'" + '"' + ">";
htmldef "n'" as "<IMG SRC='_bnj_nPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " n'" + '"' + " TITLE=" + '"' + "n'" + '"' + ">";
htmldef "o'_" as "<IMG SRC='_bnj_oPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " o'_" + '"' + " TITLE=" + '"' + "o'_" + '"' + ">";
htmldef "p'" as "<IMG SRC='_bnj_pPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " p'" + '"' + " TITLE=" + '"' + "p'" + '"' + ">";
htmldef "q'" as "<IMG SRC='_bnj_qPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " q'" + '"' + " TITLE=" + '"' + "q'" + '"' + ">";
htmldef "r'" as "<IMG SRC='_bnj_rPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " r'" + '"' + " TITLE=" + '"' + "r'" + '"' + ">";
htmldef "s'_" as "<IMG SRC='_bnj_sPrime.gif' WIDTH=11 HEIGHT=19" +
    " ALT=" + '"' + " s'" + '"' + " TITLE=" + '"' + "s'" + '"' + ">";
htmldef "t'" as "<IMG SRC='_bnj_tPrime.gif' WIDTH=11 HEIGHT=19" +
    " ALT=" + '"' + " t'" + '"' + " TITLE=" + '"' + "t'" + '"' + ">";
htmldef "u'" as "<IMG SRC='_bnj_uPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " u'" + '"' + " TITLE=" + '"' + "u'" + '"' + ">";
htmldef "v'_" as "<IMG SRC='_bnj_vPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " v'" + '"' + " TITLE=" + '"' + "v'" + '"' + ">";
htmldef "w'" as "<IMG SRC='_bnj_wPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " w'" + '"' + " TITLE=" + '"' + "w'" + '"' + ">";
htmldef "x'" as "<IMG SRC='_bnj_xPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " x'" + '"' + " TITLE=" + '"' + "x'" + '"' + ">";
htmldef "y'" as "<IMG SRC='_bnj_yPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " y'" + '"' + " TITLE=" + '"' + "y'" + '"' + ">";
htmldef "z'" as "<IMG SRC='_bnj_zPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " z'" + '"' + " TITLE=" + '"' + "z'" + '"' + ">";
althtmldef "a'" as '<SPAN CLASS=set STYLE="color:red">&#x1D44E;&prime;</SPAN>';
althtmldef "b'" as '<SPAN CLASS=set STYLE="color:red">&#x1D44F;&prime;</SPAN>';
althtmldef "c'" as '<SPAN CLASS=set STYLE="color:red">&#x1D450;&prime;</SPAN>';
althtmldef "d'" as '<SPAN CLASS=set STYLE="color:red">&#x1D451;&prime;</SPAN>';
althtmldef "e'" as '<SPAN CLASS=set STYLE="color:red">&#x1D452;&prime;</SPAN>';
althtmldef "f'" as '<SPAN CLASS=set STYLE="color:red">&#x1D453;&prime;</SPAN>';
althtmldef "g'" as '<SPAN CLASS=set STYLE="color:red">&#x1D454;&prime;</SPAN>';
althtmldef "h'" as '<SPAN CLASS=set STYLE="color:red">&#x210E;&prime;</SPAN>';
althtmldef "i'" as '<SPAN CLASS=set STYLE="color:red">&#x1D456;&prime;</SPAN>';
althtmldef "j'" as '<SPAN CLASS=set STYLE="color:red">&#x1D457;&prime;</SPAN>';
althtmldef "k'" as '<SPAN CLASS=set STYLE="color:red">&#x1D458;&prime;</SPAN>';
althtmldef "l'" as '<SPAN CLASS=set STYLE="color:red">&#x1D459;&prime;</SPAN>';
althtmldef "m'" as '<SPAN CLASS=set STYLE="color:red">&#x1D45A;&prime;</SPAN>';
althtmldef "n'" as '<SPAN CLASS=set STYLE="color:red">&#x1D45B;&prime;</SPAN>';
althtmldef "o'_" as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45C;&prime;</SPAN>';
althtmldef "p'" as '<SPAN CLASS=set STYLE="color:red">&#x1D45D;&prime;</SPAN>';
althtmldef "q'" as '<SPAN CLASS=set STYLE="color:red">&#x1D45E;&prime;</SPAN>';
althtmldef "r'" as '<SPAN CLASS=set STYLE="color:red">&#x1D45F;&prime;</SPAN>';
althtmldef "s'_" as
    '<SPAN CLASS=set STYLE="color:red">&#x1D460;&prime;</SPAN>';
althtmldef "t'" as '<SPAN CLASS=set STYLE="color:red">&#x1D461;&prime;</SPAN>';
althtmldef "u'" as '<SPAN CLASS=set STYLE="color:red">&#x1D462;&prime;</SPAN>';
althtmldef "v'_" as
     '<SPAN CLASS=set STYLE="color:red">&#x1D463;&prime;</SPAN>';
althtmldef "w'" as '<SPAN CLASS=set STYLE="color:red">&#x1D464;&prime;</SPAN>';
althtmldef "x'" as '<SPAN CLASS=set STYLE="color:red">&#x1D465;&prime;</SPAN>';
althtmldef "y'" as '<SPAN CLASS=set STYLE="color:red">&#x1D466;&prime;</SPAN>';
althtmldef "z'" as '<SPAN CLASS=set STYLE="color:red">&#x1D467;&prime;</SPAN>';
latexdef "a'" as "a'";
latexdef "b'" as "b'";
latexdef "c'" as "c'";
latexdef "d'" as "d'";
latexdef "e'" as "e'";
latexdef "f'" as "f'";
latexdef "g'" as "g'";
latexdef "h'" as "h'";
latexdef "i'" as "i'";
latexdef "j'" as "j'";
latexdef "k'" as "k'";
latexdef "l'" as "l'";
latexdef "m'" as "m'";
latexdef "n'" as "n'";
latexdef "o'_" as "o'";
latexdef "p'" as "p'";
latexdef "q'" as "q'";
latexdef "r'" as "r'";
latexdef "s'_" as "s'";
latexdef "t'" as "t'";
latexdef "u'" as "u'";
latexdef "v'_" as "v'";
latexdef "w'" as "w'";
latexdef "x'" as "x'";
latexdef "y'" as "y'";
latexdef "z'" as "z'";
htmldef 'a"' as "<IMG SRC='_bnj_aPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' a" + '"' + "' TITLE='a" + '"' + "'>";
htmldef 'b"' as "<IMG SRC='_bnj_bPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' b" + '"' + "' TITLE='b" + '"' + "'>";
htmldef 'c"' as "<IMG SRC='_bnj_cPrimePrime.gif' WIDTH=14 HEIGHT=19 " +
      " ALT=' c" + '"' + "' TITLE='c" + '"' + "'>";
htmldef 'd"' as "<IMG SRC='_bnj_dPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' d" + '"' + "' TITLE='d" + '"' + "'>";
htmldef 'e"' as "<IMG SRC='_bnj_ePrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' e" + '"' + "' TITLE='e" + '"' + "'>";
htmldef 'f"' as "<IMG SRC='_bnj_fPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' f" + '"' + "' TITLE='f" + '"' + "'>";
htmldef 'g"' as "<IMG SRC='_bnj_gPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' g" + '"' + "' TITLE='g" + '"' + "'>";
htmldef 'h"' as "<IMG SRC='_bnj_hPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' h" + '"' + "'TITLE='h" + '"' + "'>";
htmldef 'i"' as "<IMG SRC='_bnj_iPrimePrime.gif' WIDTH=13 HEIGHT=19 " +
      " ALT=' i" + '"' + "' TITLE='i" + '"' + "'>";
htmldef 'j"' as "<IMG SRC='_bnj_jPrimePrime.gif' WIDTH=14 HEIGHT=19 " +
      " ALT=' j" + '"' + "' TITLE='j" + '"' + "'>";
htmldef 'k"' as "<IMG SRC='_bnj_kPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' k" + '"' + "' TITLE='k" + '"' + "'>";
htmldef 'l"' as "<IMG SRC='_bnj_lPrimePrime.gif' WIDTH=12 HEIGHT=19 " +
      " ALT=' l" + '"' + "'TITLE='l" + '"' + "'>";
htmldef 'm"' as "<IMG SRC='_bnj_mPrimePrime.gif' WIDTH=21 HEIGHT=19 " +
      " ALT=' m" + '"' + "' TITLE='m" + '"' + "'>";
htmldef 'n"' as "<IMG SRC='_bnj_nPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' n" + '"' + "' TITLE='n" + '"' + "'>";
htmldef 'o"_' as "<IMG SRC='_bnj_oPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' o" + '"' + "'TITLE='o" + '"' + "'>";
htmldef 'p"' as "<IMG SRC='_bnj_pPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' p" + '"' + "'TITLE='p" + '"' + "'>";
htmldef 'q"' as "<IMG SRC='_bnj_qPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' q" + '"' + "'TITLE='q" + '"' + "'>";
htmldef 'r"' as "<IMG SRC='_bnj_rPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' r" + '"' + "'TITLE='r" + '"' + "'>";
htmldef 's"_' as "<IMG SRC='_bnj_sPrimePrime.gif' WIDTH=14 HEIGHT=19 " +
      " ALT=' s" + '"' + "'TITLE='s" + '"' + "'>";
htmldef 't"' as "<IMG SRC='_bnj_tPrimePrime.gif' WIDTH=14 HEIGHT=19 " +
      " ALT=' t" + '"' + "'TITLE='t" + '"' + "'>";
htmldef 'u"' as "<IMG SRC='_bnj_uPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' u" + '"' + "'TITLE='u" + '"' + "'>";
htmldef 'v"_' as "<IMG SRC='_bnj_vPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' v" + '"' + "'TITLE='v" + '"' + "'>";
htmldef 'w"' as "<IMG SRC='_bnj_wPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' w" + '"' + "'TITLE='w" + '"' + "'>";
htmldef 'x"' as "<IMG SRC='_bnj_xPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' x" + '"' + "'TITLE='x" + '"' + "'>";
htmldef 'y"' as "<IMG SRC='_bnj_yPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' y" + '"' + "'TITLE='y" + '"' + "'>";
htmldef 'z"' as "<IMG SRC='_bnj_zPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' z" + '"' + "'TITLE='z" + '"' + "'>";
althtmldef 'a"' as '<SPAN CLASS=set STYLE="color:red">&#x1D44E;&Prime;</SPAN>';
althtmldef 'b"' as '<SPAN CLASS=set STYLE="color:red">&#x1D44F;&Prime;</SPAN>';
althtmldef 'c"' as '<SPAN CLASS=set STYLE="color:red">&#x1D450;&Prime;</SPAN>';
althtmldef 'd"' as '<SPAN CLASS=set STYLE="color:red">&#x1D451;&Prime;</SPAN>';
althtmldef 'e"' as '<SPAN CLASS=set STYLE="color:red">&#x1D452;&Prime;</SPAN>';
althtmldef 'f"' as '<SPAN CLASS=set STYLE="color:red">&#x1D453;&Prime;</SPAN>';
althtmldef 'g"' as '<SPAN CLASS=set STYLE="color:red">&#x1D454;&Prime;</SPAN>';
althtmldef 'h"' as '<SPAN CLASS=set STYLE="color:red">&#x210E;&Prime;</SPAN>';
althtmldef 'i"' as '<SPAN CLASS=set STYLE="color:red">&#x1D456;&Prime;</SPAN>';
althtmldef 'j"' as '<SPAN CLASS=set STYLE="color:red">&#x1D457;&Prime;</SPAN>';
althtmldef 'k"' as '<SPAN CLASS=set STYLE="color:red">&#x1D458;&Prime;</SPAN>';
althtmldef 'l"' as '<SPAN CLASS=set STYLE="color:red">&#x1D459;&Prime;</SPAN>';
althtmldef 'm"' as '<SPAN CLASS=set STYLE="color:red">&#x1D45A;&Prime;</SPAN>';
althtmldef 'n"' as '<SPAN CLASS=set STYLE="color:red">&#x1D45B;&Prime;</SPAN>';
althtmldef 'o"_' as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45C;&Prime;</SPAN>';
althtmldef 'p"' as '<SPAN CLASS=set STYLE="color:red">&#x1D45D;&Prime;</SPAN>';
althtmldef 'q"' as '<SPAN CLASS=set STYLE="color:red">&#x1D45E;&Prime;</SPAN>';
althtmldef 'r"' as '<SPAN CLASS=set STYLE="color:red">&#x1D45F;&Prime;</SPAN>';
althtmldef 's"_' as
    '<SPAN CLASS=set STYLE="color:red">&#x1D460;&Prime;</SPAN>';
althtmldef 't"' as '<SPAN CLASS=set STYLE="color:red">&#x1D461;&Prime;</SPAN>';
althtmldef 'u"' as '<SPAN CLASS=set STYLE="color:red">&#x1D462;&Prime;</SPAN>';
althtmldef 'v"_' as
    '<SPAN CLASS=set STYLE="color:red">&#x1D463;&Prime;</SPAN>';
althtmldef 'w"' as '<SPAN CLASS=set STYLE="color:red">&#x1D464;&Prime;</SPAN>';
althtmldef 'x"' as '<SPAN CLASS=set STYLE="color:red">&#x1D465;&Prime;</SPAN>';
althtmldef 'y"' as '<SPAN CLASS=set STYLE="color:red">&#x1D466;&Prime;</SPAN>';
althtmldef 'z"' as '<SPAN CLASS=set STYLE="color:red">&#x1D467;&Prime;</SPAN>';
latexdef 'a"' as "a''";
latexdef 'b"' as "b''";
latexdef 'c"' as "c''";
latexdef 'd"' as "d''";
latexdef 'e"' as "e''";
latexdef 'f"' as "f''";
latexdef 'g"' as "g''";
latexdef 'h"' as "h''";
latexdef 'i"' as "i''";
latexdef 'j"' as "j''";
latexdef 'k"' as "k''";
latexdef 'l"' as "l''";
latexdef 'm"' as "m''";
latexdef 'n"' as "n''";
latexdef 'o"_' as "o''";
latexdef 'p"' as "p''";
latexdef 'q"' as "q''";
latexdef 'r"' as "r''";
latexdef 's"_' as "s''";
latexdef 't"' as "t''";
latexdef 'u"' as "u''";
latexdef 'v"_' as "v''";
latexdef 'w"' as "w''";
latexdef 'x"' as "x''";
latexdef 'y"' as "y''";
latexdef 'z"' as "z''";
htmldef "a0_"  as "<IMG SRC='_bnj_a0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' a0' TITLE='a0'>";
htmldef "b0_"  as "<IMG SRC='_bnj_b0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' b0' TITLE='b0'>";
htmldef "c0_" as "<IMG SRC='_bnj_c0.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' c0' TITLE='c0'>";
htmldef "d0"  as "<IMG SRC='_bnj_d0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' d0' TITLE='d0'>";
htmldef "e0"  as "<IMG SRC='_bnj_e0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' e0' TITLE='e0'>";
htmldef "f0_" as "<IMG SRC='_bnj_f0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' f0_' TITLE='f0_'>";
htmldef "g0"  as "<IMG SRC='_bnj_g0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' g0' TITLE='g0'>";
htmldef "h0"  as "<IMG SRC='_bnj_h0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' h0' TITLE='h0'>";
htmldef "i0"  as "<IMG SRC='_bnj_i0.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' i0' TITLE='i0'>";
htmldef "j0"  as "<IMG SRC='_bnj_j0.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' j0' TITLE='j0'>";
htmldef "k0"  as "<IMG SRC='_bnj_k0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' k0' TITLE='k0'>";
htmldef "l0"  as "<IMG SRC='_bnj_l0.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' l0' TITLE='l0'>";
htmldef "m0"  as "<IMG SRC='_bnj_m0.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' m0' TITLE='m0'>";
htmldef "n0_" as "<IMG SRC='_bnj_n0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' n0_' TITLE='n0_'>";
htmldef "o0_"  as "<IMG SRC='_bnj_o0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' o0_' TITLE='o0_'>";
htmldef "p0"  as "<IMG SRC='_bnj_p0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' p0' TITLE='p0'>";
htmldef "q0"  as "<IMG SRC='_bnj_q0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' q0' TITLE='q0'>";
htmldef "r0"  as "<IMG SRC='_bnj_r0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' r0' TITLE='r0'>";
htmldef "s0"  as "<IMG SRC='_bnj_s0.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' s0' TITLE='s0'>";
htmldef "t0"  as "<IMG SRC='_bnj_t0.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' t0' TITLE='t0'>";
htmldef "u0"  as "<IMG SRC='_bnj_u0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' u0' TITLE='u0'>";
htmldef "v0"  as "<IMG SRC='_bnj_v0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' v0' TITLE='v0'>";
htmldef "w0"  as "<IMG SRC='_bnj_w0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' w0' TITLE='w0'>";
htmldef "x0"  as "<IMG SRC='_bnj_x0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' x0' TITLE='x0'>";
htmldef "y0"  as "<IMG SRC='_bnj_y0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' y0' TITLE='y0'>";
htmldef "z0"  as "<IMG SRC='_bnj_z0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' z0' TITLE='z0'>";
althtmldef "a0_"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D44E;<SUB>0</SUB></SPAN>';
althtmldef "b0_"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D44F;<SUB>0</SUB></SPAN>';
althtmldef "c0_" as
    '<SPAN CLASS=set STYLE="color:red">&#x1D450;<SUB>0</SUB></SPAN>';
althtmldef "d0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D451;<SUB>0</SUB></SPAN>';
althtmldef "e0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D452;<SUB>0</SUB></SPAN>';
althtmldef "f0_" as
    '<SPAN CLASS=set STYLE="color:red">&#x1D453;<SUB>0</SUB></SPAN>';
althtmldef "g0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D454;<SUB>0</SUB></SPAN>';
althtmldef "h0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x210E;<SUB>0</SUB></SPAN>';
althtmldef "i0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D456;<SUB>0</SUB></SPAN>';
althtmldef "j0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D457;<SUB>0</SUB></SPAN>';
althtmldef "k0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D458;<SUB>0</SUB></SPAN>';
althtmldef "l0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D459;<SUB>0</SUB></SPAN>';
althtmldef "m0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45A;<SUB>0</SUB></SPAN>';
althtmldef "n0_" as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45B;<SUB>0</SUB></SPAN>';
althtmldef "o0_"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45C;<SUB>0</SUB></SPAN>';
althtmldef "p0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45D;<SUB>0</SUB></SPAN>';
althtmldef "q0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45E;<SUB>0</SUB></SPAN>';
althtmldef "r0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45F;<SUB>0</SUB></SPAN>';
althtmldef "s0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D460;<SUB>0</SUB></SPAN>';
althtmldef "t0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D461;<SUB>0</SUB></SPAN>';
althtmldef "u0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D462;<SUB>0</SUB></SPAN>';
althtmldef "v0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D463;<SUB>0</SUB></SPAN>';
althtmldef "w0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D464;<SUB>0</SUB></SPAN>';
althtmldef "x0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D465;<SUB>0</SUB></SPAN>';
althtmldef "y0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D466;<SUB>0</SUB></SPAN>';
althtmldef "z0"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D467;<SUB>0</SUB></SPAN>';
latexdef "a0_"  as "a_0";
latexdef "b0_"  as "b_0";
latexdef "c0_" as "c_0";
latexdef "d0"  as "d_0";
latexdef "e0"  as "e_0";
latexdef "f0_" as "f_0";
latexdef "g0"  as "g_0";
latexdef "h0"  as "h_0";
latexdef "i0"  as "i_0";
latexdef "j0"  as "j_0";
latexdef "k0"  as "k_0";
latexdef "l0"  as "l_0";
latexdef "m0"  as "m_0";
latexdef "n0_" as "n_0";
latexdef "o0_"  as "o_0";
latexdef "p0"  as "p_0";
latexdef "q0"  as "q_0";
latexdef "r0"  as "r_0";
latexdef "s0"  as "s_0";
latexdef "t0"  as "t_0";
latexdef "u0"  as "u_0";
latexdef "v0"  as "v_0";
latexdef "w0"  as "w_0";
latexdef "x0"  as "x_0";
latexdef "y0"  as "y_0";
latexdef "z0"  as "z_0";
htmldef "a1_"  as "<IMG SRC='_bnj_a1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' a1' TITLE='a1'>";
htmldef "b1_"  as "<IMG SRC='_bnj_b1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' b1' TITLE='b1'>";
htmldef "c1_" as "<IMG SRC='_bnj_c1.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' c1_' TITLE='c1_'>";
htmldef "d1"  as "<IMG SRC='_bnj_d1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' d1' TITLE='d1'>";
htmldef "e1"  as "<IMG SRC='_bnj_e1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' e1' TITLE='e1'>";
htmldef "f1"  as "<IMG SRC='_bnj_f1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' f1' TITLE='f1'>";
htmldef "g1"  as "<IMG SRC='_bnj_g1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' g1' TITLE='g1'>";
htmldef "h1"  as "<IMG SRC='_bnj_h1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' h1' TITLE='h1'>";
htmldef "i1"  as "<IMG SRC='_bnj_i1.gif' WIDTH=11 HEIGHT=19" +
    " ALT=' i1' TITLE='i1'>";
htmldef "j1"  as "<IMG SRC='_bnj_j1.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' j1' TITLE='j1'>";
htmldef "k1"  as "<IMG SRC='_bnj_k1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' k1' TITLE='k1'>";
htmldef "l1"  as "<IMG SRC='_bnj_l1.gif' WIDTH=10 HEIGHT=19" +
    " ALT=' l1' TITLE='l1'>";
htmldef "m1"  as "<IMG SRC='_bnj_m1.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' m1' TITLE='m1'>";
htmldef "n1"  as "<IMG SRC='_bnj_n1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' n1' TITLE='n1'>";
htmldef "o1_"  as "<IMG SRC='_bnj_o1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' o1_' TITLE='o1_'>";
htmldef "p1"  as "<IMG SRC='_bnj_p1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' p1' TITLE='p1'>";
htmldef "q1"  as "<IMG SRC='_bnj_q1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' q1' TITLE='q1'>";
htmldef "r1"  as "<IMG SRC='_bnj_r1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' r1' TITLE='r1'>";
htmldef "s1"  as "<IMG SRC='_bnj_s1.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' s1' TITLE='s1'>";
htmldef "t1"  as "<IMG SRC='_bnj_t1.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' t1' TITLE='t1'>";
htmldef "u1"  as "<IMG SRC='_bnj_u1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' u1' TITLE='u1'>";
htmldef "v1"  as "<IMG SRC='_bnj_v1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' v1' TITLE='v1'>";
htmldef "w1"  as "<IMG SRC='_bnj_w1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' w1' TITLE='w1'>";
htmldef "x1"  as "<IMG SRC='_bnj_x1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' x1' TITLE='x1'>";
htmldef "y1"  as "<IMG SRC='_bnj_y1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' y1' TITLE='y1'>";
htmldef "z1"  as "<IMG SRC='_bnj_z1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' z1' TITLE='z1'>";
althtmldef "a1_"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D44E;<SUB>1</SUB></SPAN>';
althtmldef "b1_"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D44F;<SUB>1</SUB></SPAN>';
althtmldef "c1_" as
    '<SPAN CLASS=set STYLE="color:red">&#x1D450;<SUB>1</SUB></SPAN>';
althtmldef "d1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D451;<SUB>1</SUB></SPAN>';
althtmldef "e1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D452;<SUB>1</SUB></SPAN>';
althtmldef "f1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D453;<SUB>1</SUB></SPAN>';
althtmldef "g1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D454;<SUB>1</SUB></SPAN>';
althtmldef "h1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x210E;<SUB>1</SUB></SPAN>';
althtmldef "i1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D456;<SUB>1</SUB></SPAN>';
althtmldef "j1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D457;<SUB>1</SUB></SPAN>';
althtmldef "k1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D458;<SUB>1</SUB></SPAN>';
althtmldef "l1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D459;<SUB>1</SUB></SPAN>';
althtmldef "m1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45A;<SUB>1</SUB></SPAN>';
althtmldef "n1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45B;<SUB>1</SUB></SPAN>';
althtmldef "o1_"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45C;<SUB>1</SUB></SPAN>';
althtmldef "p1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45D;<SUB>1</SUB></SPAN>';
althtmldef "q1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45E;<SUB>1</SUB></SPAN>';
althtmldef "r1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D45F;<SUB>1</SUB></SPAN>';
althtmldef "s1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D460;<SUB>1</SUB></SPAN>';
althtmldef "t1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D461;<SUB>1</SUB></SPAN>';
althtmldef "u1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D462;<SUB>1</SUB></SPAN>';
althtmldef "v1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D463;<SUB>1</SUB></SPAN>';
althtmldef "w1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D464;<SUB>1</SUB></SPAN>';
althtmldef "x1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D465;<SUB>1</SUB></SPAN>';
althtmldef "y1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D466;<SUB>1</SUB></SPAN>';
althtmldef "z1"  as
    '<SPAN CLASS=set STYLE="color:red">&#x1D467;<SUB>1</SUB></SPAN>';
latexdef "a1_"  as "a_1";
latexdef "b1_"  as "b_1";
latexdef "c1_" as "c_1";
latexdef "d1"  as "d_1";
latexdef "e1"  as "e_1";
latexdef "f1"  as "f_1";
latexdef "g1"  as "g_1";
latexdef "h1"  as "h_1";
latexdef "i1"  as "i_1";
latexdef "j1"  as "j_1";
latexdef "k1"  as "k_1";
latexdef "l1"  as "l_1";
latexdef "m1"  as "m_1";
latexdef "n1"  as "n_1";
latexdef "o1_"  as "o_1";
latexdef "p1"  as "p_1";
latexdef "q1"  as "q_1";
latexdef "r1"  as "r_1";
latexdef "s1"  as "s_1";
latexdef "t1"  as "t_1";
latexdef "u1"  as "u_1";
latexdef "v1"  as "v_1";
latexdef "w1"  as "w_1";
latexdef "x1"  as "x_1";
latexdef "y1"  as "y_1";
latexdef "z1"  as "z_1";
htmldef "A'" as "<IMG SRC='_bnj_caPrime.gif' WIDTH=15 HEIGHT=19" +
    " ALT=" + '"' + " A'" + '"' + " TITLE=" + '"' + "A'" + '"' + ">";
htmldef "B'" as "<IMG SRC='_bnj_cbPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " B'" + '"' + " TITLE=" + '"' + "B'" + '"' + ">";
htmldef "C'" as "<IMG SRC='_bnj_ccPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " C'" + '"' + " TITLE=" + '"' + "C'" + '"' + ">";
htmldef "D'" as "<IMG SRC='_bnj_cdPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " D'" + '"' + " TITLE=" + '"' + "D'" + '"' + ">";
htmldef "E'" as "<IMG SRC='_bnj_cePrime.gif' WIDTH=17 HEIGHT=19" +
    " ALT=" + '"' + " E'" + '"' + " TITLE=" + '"' + "E'" + '"' + ">";
htmldef "F'" as "<IMG SRC='_bnj_cfPrime.gif' WIDTH=17 HEIGHT=19" +
    " ALT=" + '"' + " F'" + '"' + " TITLE=" + '"' + "F'" + '"' + ">";
htmldef "G'" as "<IMG SRC='_bnj_cgPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " G'" + '"' + " TITLE=" + '"' + "G'" + '"' + ">";
htmldef "H'" as "<IMG SRC='_bnj_chPrime.gif' WIDTH=18 HEIGHT=19" +
    " ALT=" + '"' + " H'" + '"' + " TITLE=" + '"' + "H'" + '"' + ">";
htmldef "I'" as "<IMG SRC='_bnj_ciPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " I'" + '"' + " TITLE=" + '"' + "I'" + '"' + ">";
htmldef "J'" as "<IMG SRC='_bnj_cjPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " J'" + '"' + " TITLE=" + '"' + "J'" + '"' + ">";
htmldef "K'" as "<IMG SRC='_bnj_ckPrime.gif' WIDTH=18 HEIGHT=19" +
    " ALT=" + '"' + " K'" + '"' + " TITLE=" + '"' + "K'" + '"' + ">";
htmldef "L'" as "<IMG SRC='_bnj_clPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " L'" + '"' + " TITLE=" + '"' + "L'" + '"' + ">";
htmldef "M'" as "<IMG SRC='_bnj_cmPrime.gif' WIDTH=19 HEIGHT=19" +
    " ALT=" + '"' + " M'" + '"' + " TITLE=" + '"' + "M'" + '"' + ">";
htmldef "N'" as "<IMG SRC='_bnj_cnPrime.gif' WIDTH=18 HEIGHT=19" +
    " ALT=" + '"' + " N'" + '"' + " TITLE=" + '"' + "N'" + '"' + ">";
htmldef "O'" as "<IMG SRC='_bnj_coPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " O'" + '"' + " TITLE=" + '"' + "O'" + '"' + ">";
htmldef "P'" as "<IMG SRC='_bnj_cpPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " P'" + '"' + " TITLE=" + '"' + "P'" + '"' + ">";
htmldef "Q'" as "<IMG SRC='_bnj_cqPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " Q'" + '"' + " TITLE=" + '"' + "Q'" + '"' + ">";
htmldef "R'" as "<IMG SRC='_bnj_crPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " R'" + '"' + " TITLE=" + '"' + "R'" + '"' + ">";
htmldef "S'" as "<IMG SRC='_bnj_csPrime.gif' WIDTH=15 HEIGHT=19" +
    " ALT=" + '"' + " S'" + '"' + " TITLE=" + '"' + "S'" + '"' + ">";
htmldef "T'" as "<IMG SRC='_bnj_ctPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " T'" + '"' + " TITLE=" + '"' + "T'" + '"' + ">";
htmldef "U'" as "<IMG SRC='_bnj_cuPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " U'" + '"' + " TITLE=" + '"' + "U'" + '"' + ">";
htmldef "V'" as "<IMG SRC='_bnj_cvPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " V'" + '"' + " TITLE=" + '"' + "V'" + '"' + ">";
htmldef "W'" as "<IMG SRC='_bnj_cwPrime.gif' WIDTH=20 HEIGHT=19" +
    " ALT=" + '"' + " W'" + '"' + " TITLE=" + '"' + "W'" + '"' + ">";
htmldef "X'" as "<IMG SRC='_bnj_cxPrime.gif' WIDTH=17 HEIGHT=19" +
    " ALT=" + '"' + " X'" + '"' + " TITLE=" + '"' + "X'" + '"' + ">";
htmldef "Y'" as "<IMG SRC='_bnj_cyPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " Y'" + '"' + " TITLE=" + '"' + "Y'" + '"' + ">";
htmldef "Z'" as "<IMG SRC='_bnj_czPrime.gif' WIDTH=15 HEIGHT=19" +
    " ALT=" + '"' + " Z'" + '"' + " TITLE=" + '"' + "Z'" + '"' + ">";
althtmldef "A'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;&prime;</SPAN>';
althtmldef "B'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;&prime;</SPAN>';
althtmldef "C'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;&prime;</SPAN>';
althtmldef "D'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;&prime;</SPAN>';
althtmldef "E'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;&prime;</SPAN>';
althtmldef "F'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;&prime;</SPAN>';
althtmldef "G'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;&prime;</SPAN>';
althtmldef "H'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;&prime;</SPAN>';
althtmldef "I'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;&prime;</SPAN>';
althtmldef "J'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;&prime;</SPAN>';
althtmldef "K'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;&prime;</SPAN>';
althtmldef "L'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;&prime;</SPAN>';
althtmldef "M'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;&prime;</SPAN>';
althtmldef "N'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;&prime;</SPAN>';
althtmldef "O'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;&prime;</SPAN>';
althtmldef "P'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;&prime;</SPAN>';
althtmldef "Q'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;&prime;</SPAN>';
althtmldef "R'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;&prime;</SPAN>';
althtmldef "S'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;&prime;</SPAN>';
althtmldef "T'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;&prime;</SPAN>';
althtmldef "U'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;&prime;</SPAN>';
althtmldef "V'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;&prime;</SPAN>';
althtmldef "W'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;&prime;</SPAN>';
althtmldef "X'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;&prime;</SPAN>';
althtmldef "Y'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;&prime;</SPAN>';
althtmldef "Z'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;&prime;</SPAN>';
latexdef "A'" as "A'";
latexdef "B'" as "B'";
latexdef "C'" as "C'";
latexdef "D'" as "D'";
latexdef "E'" as "E'";
latexdef "F'" as "F'";
latexdef "G'" as "G'";
latexdef "H'" as "H'";
latexdef "I'" as "I'";
latexdef "J'" as "J'";
latexdef "K'" as "K'";
latexdef "L'" as "L'";
latexdef "M'" as "M'";
latexdef "N'" as "N'";
latexdef "O'" as "O'";
latexdef "P'" as "P'";
latexdef "Q'" as "Q'";
latexdef "R'" as "R'";
latexdef "S'" as "S'";
latexdef "T'" as "T'";
latexdef "U'" as "U'";
latexdef "V'" as "V'";
latexdef "W'" as "W'";
latexdef "X'" as "X'";
latexdef "Y'" as "Y'";
latexdef "Z'" as "Z'";
htmldef 'A"' as "<IMG SRC='_bnj_caPrimePrime.gif' WIDTH=18 HEIGHT=19 " +
      " ALT=' A" + '"' + "'TITLE='A" + '"' + "'>";
htmldef 'B"' as "<IMG SRC='_bnj_cbPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' B" + '"' + "'TITLE='B" + '"' + "'>";
htmldef 'C"' as "<IMG SRC='_bnj_ccPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' C" + '"' + "'TITLE='C" + '"' + "'>";
htmldef 'D"' as "<IMG SRC='_bnj_cdPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' D" + '"' + "'TITLE='D" + '"' + "'>";
htmldef 'E"' as "<IMG SRC='_bnj_cePrimePrime.gif' WIDTH=20 HEIGHT=19 " +
      " ALT=' E" + '"' + "'TITLE='E" + '"' + "'>";
htmldef 'F"' as "<IMG SRC='_bnj_cfPrimePrime.gif' WIDTH=20 HEIGHT=19 " +
      " ALT=' F" + '"' + "'TITLE='F" + '"' + "'>";
htmldef 'G"' as "<IMG SRC='_bnj_cgPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' G" + '"' + "'TITLE='G" + '"' + "'>";
htmldef 'H"' as "<IMG SRC='_bnj_chPrimePrime.gif' WIDTH=21 HEIGHT=19 " +
      " ALT=' H" + '"' + "'TITLE='H" + '"' + "'>";
htmldef 'I"' as "<IMG SRC='_bnj_ciPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' I" + '"' + "'TITLE='I" + '"' + "'>";
htmldef 'J"' as "<IMG SRC='_bnj_cjPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' J" + '"' + "'TITLE='J" + '"' + "'>";
htmldef 'K"' as "<IMG SRC='_bnj_ckPrimePrime.gif' WIDTH=21 HEIGHT=19 " +
      " ALT=' K" + '"' + "'TITLE='K" + '"' + "'>";
htmldef 'L"' as "<IMG SRC='_bnj_clPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' L" + '"' + "'TITLE='L" + '"' + "'>";
htmldef 'M"' as "<IMG SRC='_bnj_cmPrimePrime.gif' WIDTH=22 HEIGHT=19 " +
      " ALT=' M" + '"' + "'TITLE='M" + '"' + "'>";
htmldef 'N"' as "<IMG SRC='_bnj_cnPrimePrime.gif' WIDTH=21 HEIGHT=19 " +
      " ALT=' N" + '"' + "'TITLE='N" + '"' + "'>";
htmldef 'O"' as "<IMG SRC='_bnj_coPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' O" + '"' + "'TITLE='O" + '"' + "'>";
htmldef 'P"' as "<IMG SRC='_bnj_cpPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' P" + '"' + "'TITLE='P" + '"' + "'>";
htmldef 'Q"' as "<IMG SRC='_bnj_cqPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' Q" + '"' + "'TITLE='Q" + '"' + "'>";
htmldef 'R"' as "<IMG SRC='_bnj_crPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' R" + '"' + "'TITLE='R" + '"' + "'>";
htmldef 'S"' as "<IMG SRC='_bnj_csPrimePrime.gif' WIDTH=18 HEIGHT=19 " +
      " ALT=' S" + '"' + "'TITLE='S" + '"' + "'>";
htmldef 'T"' as "<IMG SRC='_bnj_ctPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' T" + '"' + "'TITLE='T" + '"' + "'>";
htmldef 'U"' as "<IMG SRC='_bnj_cuPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' U" + '"' + "'TITLE='U" + '"' + "'>";
htmldef 'V"' as "<IMG SRC='_bnj_cvPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' V" + '"' + "'TITLE='V" + '"' + "'>";
htmldef 'W"' as "<IMG SRC='_bnj_cwPrimePrime.gif' WIDTH=23 HEIGHT=19 " +
      " ALT=' W" + '"' + "'TITLE='W" + '"' + "'>";
htmldef 'X"' as "<IMG SRC='_bnj_cxPrimePrime.gif' WIDTH=20 HEIGHT=19 " +
      " ALT=' X" + '"' + "'TITLE='X" + '"' + "'>";
htmldef 'Y"' as "<IMG SRC='_bnj_cyPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' Y" + '"' + "'TITLE='Y" + '"' + "'>";
htmldef 'Z"' as "<IMG SRC='_bnj_czPrimePrime.gif' WIDTH=18 HEIGHT=19 " +
      " ALT=' Z" + '"' + "'TITLE='Z" + '"' + "'>";
althtmldef 'A"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;&Prime;</SPAN>';
althtmldef 'B"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;&Prime;</SPAN>';
althtmldef 'C"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;&Prime;</SPAN>';
althtmldef 'D"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;&Prime;</SPAN>';
althtmldef 'E"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;&Prime;</SPAN>';
althtmldef 'F"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;&Prime;</SPAN>';
althtmldef 'G"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;&Prime;</SPAN>';
althtmldef 'H"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;&Prime;</SPAN>';
althtmldef 'I"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;&Prime;</SPAN>';
althtmldef 'J"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;&Prime;</SPAN>';
althtmldef 'K"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;&Prime;</SPAN>';
althtmldef 'L"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;&Prime;</SPAN>';
althtmldef 'M"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;&Prime;</SPAN>';
althtmldef 'N"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;&Prime;</SPAN>';
althtmldef 'O"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;&Prime;</SPAN>';
althtmldef 'P"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;&Prime;</SPAN>';
althtmldef 'Q"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;&Prime;</SPAN>';
althtmldef 'R"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;&Prime;</SPAN>';
althtmldef 'S"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;&Prime;</SPAN>';
althtmldef 'T"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;&Prime;</SPAN>';
althtmldef 'U"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;&Prime;</SPAN>';
althtmldef 'V"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;&Prime;</SPAN>';
althtmldef 'W"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;&Prime;</SPAN>';
althtmldef 'X"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;&Prime;</SPAN>';
althtmldef 'Y"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;&Prime;</SPAN>';
althtmldef 'Z"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;&Prime;</SPAN>';
latexdef 'A"' as "A''";
latexdef 'B"' as "B''";
latexdef 'C"' as "C''";
latexdef 'D"' as "D''";
latexdef 'E"' as "E''";
latexdef 'F"' as "F''";
latexdef 'G"' as "G''";
latexdef 'H"' as "H''";
latexdef 'I"' as "I''";
latexdef 'J"' as "J''";
latexdef 'K"' as "K''";
latexdef 'L"' as "L''";
latexdef 'M"' as "M''";
latexdef 'N"' as "N''";
latexdef 'O"' as "O''";
latexdef 'P"' as "P''";
latexdef 'Q"' as "Q''";
latexdef 'R"' as "R''";
latexdef 'S"' as "S''";
latexdef 'T"' as "T''";
latexdef 'U"' as "U''";
latexdef 'V"' as "V''";
latexdef 'W"' as "W''";
latexdef 'X"' as "X''";
latexdef 'Y"' as "Y''";
latexdef 'Z"' as "Z''";
htmldef "A0" as "<IMG SRC='_bnj_ca0.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' A0' TITLE='A0'>";
htmldef "B0" as "<IMG SRC='_bnj_cb0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' B0' TITLE='B0'>";
htmldef "C0" as "<IMG SRC='_bnj_cc0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' C0' TITLE='C0'>";
htmldef "D0" as "<IMG SRC='_bnj_cd0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' D0' TITLE='D0'>";
htmldef "E0" as "<IMG SRC='_bnj_ce0.gif' WIDTH=20 HEIGHT=19" +
    " ALT=' E0' TITLE='E0'>";
htmldef "F0" as "<IMG SRC='_bnj_cf0.gif' WIDTH=20 HEIGHT=19" +
    " ALT=' F0' TITLE='F0'>";
htmldef "G0" as "<IMG SRC='_bnj_cg0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' G0' TITLE='G0'>";
htmldef "H0" as "<IMG SRC='_bnj_ch0.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' H0' TITLE='H0'>";
htmldef "I0" as "<IMG SRC='_bnj_ci0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' I0' TITLE='I0'>";
htmldef "J0" as "<IMG SRC='_bnj_cj0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' J0' TITLE='J0'>";
htmldef "K0" as "<IMG SRC='_bnj_ck0.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' K0' TITLE='K0'>";
htmldef "L0" as "<IMG SRC='_bnj_cl0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' L0' TITLE='L0'>";
htmldef "M0" as "<IMG SRC='_bnj_cm0.gif' WIDTH=22 HEIGHT=19" +
    " ALT=' M0' TITLE='M0'>";
htmldef "N0" as "<IMG SRC='_bnj_cn0.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' N0' TITLE='N0'>";
htmldef "O0" as "<IMG SRC='_bnj_co0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' O0' TITLE='O0'>";
htmldef "P0" as "<IMG SRC='_bnj_cp0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' P0' TITLE='P0'>";
htmldef "Q0" as "<IMG SRC='_bnj_cq0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' Q0' TITLE='Q0'>";
htmldef "R0" as "<IMG SRC='_bnj_cr0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' R0' TITLE='R0'>";
htmldef "S0" as "<IMG SRC='_bnj_cs0.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' S0' TITLE='S0'>";
htmldef "T0" as "<IMG SRC='_bnj_ct0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' T0' TITLE='T0'>";
htmldef "U0" as "<IMG SRC='_bnj_cu0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' U0' TITLE='U0'>";
htmldef "V0" as "<IMG SRC='_bnj_cv0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' V0' TITLE='V0'>";
htmldef "W0" as "<IMG SRC='_bnj_cw0.gif' WIDTH=23 HEIGHT=19" +
    " ALT=' W0' TITLE='W0'>";
htmldef "X0" as "<IMG SRC='_bnj_cx0.gif' WIDTH=20 HEIGHT=19" +
    " ALT=' X0' TITLE='X0'>";
htmldef "Y0" as "<IMG SRC='_bnj_cy0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' Y0' TITLE='Y0'>";
htmldef "Z0" as "<IMG SRC='_bnj_cz0.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' Z0' TITLE='Z0'>";
althtmldef "A0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;<SUB>0</SUB></SPAN>';
althtmldef "B0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;<SUB>0</SUB></SPAN>';
althtmldef "C0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;<SUB>0</SUB></SPAN>';
althtmldef "D0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;<SUB>0</SUB></SPAN>';
althtmldef "E0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;<SUB>0</SUB></SPAN>';
althtmldef "F0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;<SUB>0</SUB></SPAN>';
althtmldef "G0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;<SUB>0</SUB></SPAN>';
althtmldef "H0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;<SUB>0</SUB></SPAN>';
althtmldef "I0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;<SUB>0</SUB></SPAN>';
althtmldef "J0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;<SUB>0</SUB></SPAN>';
althtmldef "K0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;<SUB>0</SUB></SPAN>';
althtmldef "L0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;<SUB>0</SUB></SPAN>';
althtmldef "M0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;<SUB>0</SUB></SPAN>';
althtmldef "N0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;<SUB>0</SUB></SPAN>';
althtmldef "O0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;<SUB>0</SUB></SPAN>';
althtmldef "P0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;<SUB>0</SUB></SPAN>';
althtmldef "Q0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;<SUB>0</SUB></SPAN>';
althtmldef "R0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;<SUB>0</SUB></SPAN>';
althtmldef "S0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;<SUB>0</SUB></SPAN>';
althtmldef "T0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;<SUB>0</SUB></SPAN>';
althtmldef "U0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;<SUB>0</SUB></SPAN>';
althtmldef "V0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;<SUB>0</SUB></SPAN>';
althtmldef "W0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;<SUB>0</SUB></SPAN>';
althtmldef "X0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;<SUB>0</SUB></SPAN>';
althtmldef "Y0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;<SUB>0</SUB></SPAN>';
althtmldef "Z0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;<SUB>0</SUB></SPAN>';
latexdef "A0" as "A_0";
latexdef "B0" as "B_0";
latexdef "C0" as "C_0";
latexdef "D0" as "D_0";
latexdef "E0" as "E_0";
latexdef "F0" as "F_0";
latexdef "G0" as "G_0";
latexdef "H0" as "H_0";
latexdef "I0" as "I_0";
latexdef "J0" as "J_0";
latexdef "K0" as "K_0";
latexdef "L0" as "L_0";
latexdef "M0" as "M_0";
latexdef "N0" as "N_0";
latexdef "O0" as "O_0";
latexdef "P0" as "P_0";
latexdef "Q0" as "Q_0";
latexdef "R0" as "R_0";
latexdef "S0" as "S_0";
latexdef "T0" as "T_0";
latexdef "U0" as "U_0";
latexdef "V0" as "V_0";
latexdef "W0" as "W_0";
latexdef "X0" as "X_0";
latexdef "Y0" as "Y_0";
latexdef "Z0" as "Z_0";
htmldef "A1_"  as "<IMG SRC='_bnj_ca1.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' A1' TITLE='A1'>";
htmldef "B1_"  as "<IMG SRC='_bnj_cb1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' B1' TITLE='B1'>";
htmldef "C1_"  as "<IMG SRC='_bnj_cc1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' C1' TITLE='C1'>";
htmldef "D1_"  as "<IMG SRC='_bnj_cd1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' D1' TITLE='D1'>";
htmldef "E1"  as "<IMG SRC='_bnj_ce1.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' E1' TITLE='E1'>";
htmldef "F1_"  as "<IMG SRC='_bnj_cf1.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' F1' TITLE='F1'>";
htmldef "G1_"  as "<IMG SRC='_bnj_cg1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' G1' TITLE='G1'>";
htmldef "H1_"  as "<IMG SRC='_bnj_ch1.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' H1' TITLE='H1'>";
htmldef "I1_"  as "<IMG SRC='_bnj_ci1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' I1' TITLE='I1'>";
htmldef "J1"  as "<IMG SRC='_bnj_cj1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' J1' TITLE='J1'>";
htmldef "K1"  as "<IMG SRC='_bnj_ck1.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' K1' TITLE='K1'>";
htmldef "L1_"  as "<IMG SRC='_bnj_cl1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' L1' TITLE='L1'>";
htmldef "M1_"  as "<IMG SRC='_bnj_cm1.gif' WIDTH=20 HEIGHT=19" +
    " ALT=' M1' TITLE='M1'>";
htmldef "N1"  as "<IMG SRC='_bnj_cn1.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' N1' TITLE='N1'>";
htmldef "O1_"  as "<IMG SRC='_bnj_co1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' O1_' TITLE='O1_'>";
htmldef "P1"  as "<IMG SRC='_bnj_cp1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' P1' TITLE='P1'>";
htmldef "Q1"  as "<IMG SRC='_bnj_cq1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' Q1' TITLE='Q1'>";
htmldef "R1_" as "<IMG SRC='_bnj_cr1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' R1_' TITLE='R1_'>";
htmldef "S1_"  as "<IMG SRC='_bnj_cs1.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' S1' TITLE='S1'>";
htmldef "T1"  as "<IMG SRC='_bnj_ct1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' T1' TITLE='T1'>";
htmldef "U1"  as "<IMG SRC='_bnj_cu1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' U1' TITLE='U1'>";
htmldef "V1_"  as "<IMG SRC='_bnj_cv1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' V1' TITLE='V1'>";
htmldef "W1"  as "<IMG SRC='_bnj_cw1.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' W1' TITLE='W1'>";
htmldef "X1"  as "<IMG SRC='_bnj_cx1.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' X1' TITLE='X1'>";
htmldef "Y1"  as "<IMG SRC='_bnj_cy1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' Y1' TITLE='Y1'>";
htmldef "Z1"  as "<IMG SRC='_bnj_cz1.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' Z1' TITLE='Z1'>";
althtmldef "A1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;<SUB>1</SUB></SPAN>';
althtmldef "B1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;<SUB>1</SUB></SPAN>';
althtmldef "C1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;<SUB>1</SUB></SPAN>';
althtmldef "D1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;<SUB>1</SUB></SPAN>';
althtmldef "E1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;<SUB>1</SUB></SPAN>';
althtmldef "F1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;<SUB>1</SUB></SPAN>';
althtmldef "G1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;<SUB>1</SUB></SPAN>';
althtmldef "H1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;<SUB>1</SUB></SPAN>';
althtmldef "I1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;<SUB>1</SUB></SPAN>';
althtmldef "J1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;<SUB>1</SUB></SPAN>';
althtmldef "K1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;<SUB>1</SUB></SPAN>';
althtmldef "L1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;<SUB>1</SUB></SPAN>';
althtmldef "M1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;<SUB>1</SUB></SPAN>';
althtmldef "N1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;<SUB>1</SUB></SPAN>';
althtmldef "O1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;<SUB>1</SUB></SPAN>';
althtmldef "P1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;<SUB>1</SUB></SPAN>';
althtmldef "Q1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;<SUB>1</SUB></SPAN>';
althtmldef "R1_" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;<SUB>1</SUB></SPAN>';
althtmldef "S1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;<SUB>1</SUB></SPAN>';
althtmldef "T1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;<SUB>1</SUB></SPAN>';
althtmldef "U1"  as
   '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;<SUB>1</SUB></SPAN>';
althtmldef "V1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;<SUB>1</SUB></SPAN>';
althtmldef "W1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;<SUB>1</SUB></SPAN>';
althtmldef "X1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;<SUB>1</SUB></SPAN>';
althtmldef "Y1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;<SUB>1</SUB></SPAN>';
althtmldef "Z1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;<SUB>1</SUB></SPAN>';
latexdef "A1_"  as "A_1";
latexdef "B1_"  as "B_1";
latexdef "C1_"  as "C_1";
latexdef "D1_"  as "D_1";
latexdef "E1"  as "E_1";
latexdef "F1_"  as "F_1";
latexdef "G1_"  as "G_1";
latexdef "H1_"  as "H_1";
latexdef "I1_"  as "I_1";
latexdef "J1"  as "J_1";
latexdef "K1"  as "K_1";
latexdef "L1_"  as "L_1";
latexdef "M1_"  as "M_1";
latexdef "N1"  as "N_1";
latexdef "O1_"  as "O_1";
latexdef "P1"  as "P_1";
latexdef "Q1"  as "Q_1";
latexdef "R1_" as "R_1";
latexdef "S1_"  as "S_1";
latexdef "T1"  as "T_1";
latexdef "U1"  as "U_1";
latexdef "V1_"  as "V_1";
latexdef "W1"  as "W_1";
latexdef "X1"  as "X_1";
latexdef "Y1"  as "Y_1";
latexdef "Z1"  as "Z_1";
/*
htmldef "_fns" as
    " <IMG SRC='_fns.gif' WIDTH=19 HEIGHT=19 ALT=' fns' TITLE='fns'> ";
  althtmldef "_fns" as " fns ";
  latexdef "_fns" as "{\rm fns\;}";
*/
htmldef "_pred" as
    " <IMG SRC='_pred.gif' WIDTH=30 HEIGHT=19 ALT=' pred' TITLE='pred'>";
  althtmldef "_pred" as " pred";
  latexdef "_pred" as "{\rm pred}";
htmldef "_Se" as
    " <IMG SRC='_cse.gif' WIDTH=15 HEIGHT=19 ALT=' Se' TITLE='Se'> ";
  althtmldef "_Se" as " Se ";
  latexdef "_Se" as "{\rm \;Se\;}";
htmldef "_FrSe" as
    " <IMG SRC='_frse.gif' WIDTH=30 HEIGHT=19 ALT=' FrSe' TITLE='FrSe'> ";
  althtmldef "_FrSe" as " FrSe ";
  latexdef "_FrSe" as "{\rm \;FrSe\;}";
htmldef "_trCl" as
    " <IMG SRC='_trcl.gif' WIDTH=26 HEIGHT=19 ALT=' trCl' TITLE='trCl'>";
  althtmldef "_trCl" as " trCl";
  latexdef "_trCl" as "{\rm trCl}";
htmldef "_TrFo" as
    " <IMG SRC='_trfo.gif' WIDTH=32 HEIGHT=19 ALT=' TrFo' TITLE='TrFo'>";
  althtmldef "_TrFo" as " TrFo";
  latexdef "_TrFo" as "{\rm TrFo}";
/* End of Jonathan Ben-Naim's mathbox */

/* Mathbox of Norm Megill */
htmldef "LSAtoms" as "LSAtoms";
  althtmldef "LSAtoms" as "LSAtoms";
  latexdef "LSAtoms" as "{\rm LSAtoms}";
htmldef "LSHyp" as "LSHyp";
  althtmldef "LSHyp" as "LSHyp";
  latexdef "LSHyp" as "{\rm LSHyp}";
htmldef "<oL" as
    " <IMG SRC='lessdot.gif' WIDTH=11 HEIGHT=19 "
    + "ALT=' &lt;oL' TITLE='&lt;oL'><SUB>L</SUB> ";
  althtmldef "<oL" as ' &#8918;<SUB>L</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "<oL" as "\lessdot_{\rm L}";
htmldef "LFnl" as "LFnl";
  althtmldef "LFnl" as "LFnl";
  latexdef "LFnl" as "{\rm LFnl}";
htmldef "LKer" as "LKer";
  althtmldef "LKer" as "LKer";
  latexdef "LKer" as "{\rm LKer}";
htmldef "LDual" as "LDual";
  althtmldef "LDual" as "LDual";
  latexdef "LDual" as "{\rm LDual}";
htmldef "OP" as "<IMG SRC='_op.gif' WIDTH=20 HEIGHT=19 ALT=' OP' TITLE='OP'>";
  althtmldef "OP" as "OP";
  latexdef "OP" as "{\rm OP}";
htmldef "cm" as
    "<IMG SRC='_rmcm.gif' WIDTH=19 HEIGHT=19 ALT=' cm' TITLE='cm'>";
  althtmldef "cm" as "cm";
  latexdef "cm" as "{\rm cm}";
htmldef "OL" as "<IMG SRC='_ol.gif' WIDTH=20 HEIGHT=19 ALT=' OL' TITLE='OL'>";
  althtmldef "OL" as "OL";
  latexdef "OL" as "{\rm OL}";
htmldef "OML" as
    "<IMG SRC='_oml.gif' WIDTH=32 HEIGHT=19 ALT=' OML' TITLE='OML'>";
  althtmldef "OML" as "OML";
  latexdef "OML" as "{\rm OML}";
htmldef "<o" as
    " <IMG SRC='lessdot.gif' WIDTH=11 HEIGHT=19 "
    + "ALT=' &lt;o' TITLE='&lt;o'> ";
  althtmldef "<o" as ' &#8918; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "<o" as '\lessdot';
htmldef "Atoms" as
    "<IMG SRC='_atoms.gif' WIDTH=41 HEIGHT=19 ALT=' Atoms' TITLE='Atoms'>";
  althtmldef "Atoms" as "Atoms";
  latexdef "Atoms" as "{\rm Atoms}";
htmldef "AtLat" as
    "<IMG SRC='_atlat.gif' WIDTH=39 HEIGHT=19 ALT=' AtLat' TITLE='AtLat'>";
  althtmldef "AtLat" as "AtLat";
  latexdef "AtLat" as "{\rm AtLat}";
/*
htmldef "AtsLat" as "AtsLat"; althtmldef "AtsLat" as "AtsLat";
*/
htmldef "CvLat" as
    "<IMG SRC='_cvlat.gif' WIDTH=41 HEIGHT=19 ALT=' CvLat' TITLE='CvLat'>";
  althtmldef "CvLat" as "CvLat";
  latexdef "CvLat" as "{\rm CvLat}";
htmldef "HL" as "<IMG SRC='_hl.gif' WIDTH=19 HEIGHT=19 ALT=' HL' TITLE='HL'>";
  althtmldef "HL" as "HL";
  latexdef "HL" as "{\rm HL}";
/*
htmldef "ser" as "ser";
  althtmldef "ser" as "ser";
  latexdef "ser" as "{\rm ser}";
htmldef "fcard" as "fcard"; althtmldef "fcard" as "fcard";
htmldef "idsumf" as "idsumf"; althtmldef "idsumf" as "idsumf";
htmldef "idsum" as "idsum"; althtmldef "idsum" as "idsum";
htmldef "C_rng" as "C_rng"; althtmldef "C_rng" as "C_rng";
htmldef "-vNEW" as "-vNEW"; althtmldef "-vNEW" as "-vNEW";
htmldef "RVecNEW" as "RVecNEW"; althtmldef "RVecNEW" as "RVecNEW";
htmldef "+ss" as
    "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='_subss.gif' WIDTH=10 HEIGHT=19 ALT=' ss' TITLE='ss'>";
  althtmldef "+ss" as "+<SUB>ss</SUB>";
  latexdef "+ss" as "+_{\rm ss}";
htmldef "SubSpNEW" as "SubSpNEW"; althtmldef "SubSpNEW" as "SubSpNEW";
htmldef "spanNEW" as "spanNEW"; althtmldef "spanNEW" as "spanNEW";
htmldef "o+" as "o+"; althtmldef "o+" as "o+";
htmldef "Ev" as "Ev"; althtmldef "Ev" as "Ev";
htmldef "/v" as "/v"; althtmldef "/v" as "/v";
htmldef "normv" as "normv"; althtmldef "normv" as "normv";
*/
htmldef "LLines" as
    "<IMG SRC='_llines.gif' WIDTH=43 HEIGHT=19 ALT=' LLines' TITLE='LLines'>";
  althtmldef "LLines" as "LLines";
  latexdef "LLines" as "{\rm LLines}";
htmldef "LPlanes" as
  "<IMG SRC='_lplanes.gif' WIDTH=51 HEIGHT=19 ALT=' LPlanes' TITLE='LPlanes'>";
  althtmldef "LPlanes" as "LPlanes";
  latexdef "LPlanes" as "{\rm LPlanes}";
htmldef "LVols" as
    "<IMG SRC='_lvols.gif' WIDTH=36 HEIGHT=19 ALT=' LVols' TITLE='LVols'>";
  althtmldef "LVols" as "LVols";
  latexdef "LVols" as "{\rm LVols}";
htmldef "Lines" as
    "<IMG SRC='_lines.gif' WIDTH=34 HEIGHT=19 ALT=' Lines' TITLE='Lines'>";
  althtmldef "Lines" as "Lines";
  latexdef "Lines" as "{\rm Lines}";
htmldef "Points" as
    "<IMG SRC='_points.gif' WIDTH=40 HEIGHT=19 ALT=' Points' TITLE='Points'>";
  althtmldef "Points" as "Points";
  latexdef "Points" as "{\rm Points}";
htmldef "PSubSp" as
    "<IMG SRC='_psubsp.gif' WIDTH=49 HEIGHT=19 ALT=' PSubSp' TITLE='PSubSp'>";
  althtmldef "PSubSp" as "PSubSp";
  latexdef "PSubSp" as "{\rm PSubSp}";
htmldef "pmap" as
    "<IMG SRC='_pmap.gif' WIDTH=36 HEIGHT=19 ALT=' pmap' TITLE='pmap'>";
  althtmldef "pmap" as "pmap";
  latexdef "pmap" as "{\rm pmap}";
htmldef "+P" as
    "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='subcp.gif' WIDTH=8 HEIGHT=19 ALT=' P' TITLE='P'>";
  althtmldef "+P" as "+<SUB>&#x1D443;</SUB>";
  latexdef "+P" as "+_P";
htmldef "PCl" as
    "<IMG SRC='_pcl.gif' WIDTH=23 HEIGHT=19 ALT=' PCl' TITLE='PCl'>";
  althtmldef "PCl" as "PCl";
  latexdef "PCl" as "{\rm PCl}";
htmldef "_|_P" as
    "<IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT=' _|_' TITLE='_|_'>" +
    "<IMG SRC='subcp.gif' WIDTH=8 HEIGHT=19 ALT=' P' TITLE='P'>";
  althtmldef "_|_P" as "&#8869;<SUB>&#x1D443;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "_|_P" as "\perp_P";
htmldef "PSubCl" as
    "<IMG SRC='_psubcl.gif' WIDTH=47 HEIGHT=19 ALT=' PSubCl' TITLE='PSubCl'>";
  althtmldef "PSubCl" as "PSubCl";
  latexdef "PSubCl" as "{\rm PSubCl}";
/*
htmldef "sumP" as "sumP"; althtmldef "sumP" as "sumP";
htmldef "Indep" as "Indep"; althtmldef "Indep" as "Indep";
htmldef "BasesP" as "BasesP"; althtmldef "BasesP" as "BasesP";
htmldef "rankP" as "rankP"; althtmldef "rankP" as "rankP";
htmldef "PHyp" as "PHyp"; althtmldef "PHyp" as "PHyp";
htmldef "ww" as "ww"; althtmldef "ww" as "ww";
*/
htmldef "LHyp" as
    "<IMG SRC='_lhyp.gif' WIDTH=35 HEIGHT=19 ALT=' LHyp' TITLE='LHyp'>";
  althtmldef "LHyp" as "LHyp";
  latexdef "LHyp" as "{\rm LHyp}";
htmldef "LAut" as
    "<IMG SRC='_laut.gif' WIDTH=33 HEIGHT=19 ALT=' LAut' TITLE='LAut'>";
  althtmldef "LAut" as "LAut";
  latexdef "LAut" as "{\rm LAut}";
htmldef "WAtoms" as
    "<IMG SRC='_watoms.gif' WIDTH=53 HEIGHT=19 ALT=' WAtoms' TITLE='WAtoms'>";
  althtmldef "WAtoms" as "WAtoms";
  latexdef "WAtoms" as "{\rm WAtoms}";
htmldef "PAut" as
    "<IMG SRC='_paut.gif' WIDTH=30 HEIGHT=19 ALT=' PAut' TITLE='PAut'>";
  althtmldef "PAut" as "PAut";
  latexdef "PAut" as "{\rm PAut}";
htmldef "LDil" as
    "<IMG SRC='_ldil.gif' WIDTH=27 HEIGHT=19 ALT=' LDil' TITLE='LDil'>";
  althtmldef "LDil" as "LDil";
  latexdef "LDil" as "{\rm LDil}";
htmldef "LTrn" as
    "<IMG SRC='_ltrn.gif' WIDTH=33 HEIGHT=19 ALT=' LTrn' TITLE='LTrn'>";
  althtmldef "LTrn" as "LTrn";
  latexdef "LTrn" as "{\rm LTrn}";
htmldef "Dil" as
    "<IMG SRC='_dil.gif' WIDTH=18 HEIGHT=19 ALT=' Dil' TITLE='Dil'>";
  althtmldef "Dil" as "Dil";
  latexdef "Dil" as "{\rm Dil}";
htmldef "Trn" as
    "<IMG SRC='_trn.gif' WIDTH=23 HEIGHT=19 ALT=' Trn' TITLE='Trn'>";
  althtmldef "Trn" as "Trn";
  latexdef "Trn" as "{\rm Trn}";
/*
htmldef "trP" as "trP"; althtmldef "trP" as "trP";
*/
htmldef "trL" as
    "<IMG SRC='_trl.gif' WIDTH=21 HEIGHT=19 ALT=' trL' TITLE='trL'>";
  althtmldef "trL" as "trL";
  latexdef "trL" as "{\rm trL}";
htmldef "TGrp" as
    "<IMG SRC='_tgrp.gif' WIDTH=35 HEIGHT=19 ALT=' TGrp' TITLE='TGrp'>";
  althtmldef "TGrp" as "TGrp";
  latexdef "TGrp" as "{\rm TGrp}";
htmldef "TEndo" as
    "<IMG SRC='_tendo.gif' WIDTH=42 HEIGHT=19 ALT=' TEndo' TITLE='TEndo'>";
  althtmldef "TEndo" as "TEndo";
  latexdef "TEndo" as "{\rm TEndo}";
htmldef "EDRing" as
    "<IMG SRC='_edring.gif' WIDTH=49 HEIGHT=19 ALT=' EDRing' TITLE='EDRing'>";
  althtmldef "EDRing" as "EDRing";
  latexdef "EDRing" as "{\rm EDRing}";
htmldef "EDRingR" as
    "<IMG SRC='_edring.gif' WIDTH=49 HEIGHT=19 ALT=' EDRing' TITLE='EDRing'>" +
    "<IMG SRC='subcr.gif' WIDTH=9 HEIGHT=19 ALT=' R' TITLE='R'>";
  althtmldef "EDRingR" as "EDRing<SUB>R</SUB>";
  latexdef "EDRingR" as "{\rm EDRing}_R";
htmldef "DVecA" as
    "<IMG SRC='_dveca.gif' WIDTH=44 HEIGHT=19 ALT=' DVecA' TITLE='DVecA'>";
  althtmldef "DVecA" as "DVecA";
  latexdef "DVecA" as "{\rm DVecA}";
htmldef "DIsoA" as
    "<IMG SRC='_disoa.gif' WIDTH=37 HEIGHT=19 ALT=' DIsoA' TITLE='DIsoA'>";
  althtmldef "DIsoA" as "DIsoA";
  latexdef "DIsoA" as "{\rm DIsoA}";
htmldef "DVecH" as
    "<IMG SRC='_dvech.gif' WIDTH=44 HEIGHT=19 ALT=' DVecH' TITLE='DVecH'>";
  althtmldef "DVecH" as "DVecH";
  latexdef "DVecH" as "{\rm DVecH}";
htmldef "ocA" as
    "<IMG SRC='_oca.gif' WIDTH=24 HEIGHT=19 ALT=' ocA' TITLE='ocA'>";
  althtmldef "ocA" as "ocA";
  latexdef "ocA" as "{\rm ocA}";
htmldef "vA" as "<IMG SRC='_va.gif' WIDTH=16 HEIGHT=19 ALT=' vA' TITLE='vA'>";
  althtmldef "vA" as "vA";
  latexdef "vA" as "{\rm vA}";
htmldef "DIsoB" as
    "<IMG SRC='_disob.gif' WIDTH=36 HEIGHT=19 ALT=' DIsoB' TITLE='DIsoB'>";
  althtmldef "DIsoB" as "DIsoB";
  latexdef "DIsoB" as "{\rm DIsoB}";
htmldef "DIsoC" as
    "<IMG SRC='_disoc.gif' WIDTH=37 HEIGHT=19 ALT=' DIsoC' TITLE='DIsoC'>";
  althtmldef "DIsoC" as "DIsoC";
  latexdef "DIsoC" as "{\rm DIsoC}";
htmldef "DIsoH" as
    "<IMG SRC='_disoh.gif' WIDTH=37 HEIGHT=19 ALT=' DIsoH' TITLE='DIsoH'>";
  althtmldef "DIsoH" as "DIsoH";
  latexdef "DIsoH" as "{\rm DIsoH}";
htmldef "ocH" as
    "<IMG SRC='_och.gif' WIDTH=24 HEIGHT=19 ALT=' ocH' TITLE='ocH'>";
  althtmldef "ocH" as "ocH";
  latexdef "ocH" as "{\rm ocH}";
htmldef "joinH" as "joinH";
  althtmldef "joinH" as "joinH";
  latexdef "joinH" as "{\rm joinH}";
htmldef "LPol" as "LPol";
  althtmldef "LPol" as "LPol";
  latexdef "LPol" as "{\rm LPol}";
htmldef "LCDual" as "LCDual";
  althtmldef "LCDual" as "LCDual";
  latexdef "LCDual" as "{\rm LCDual}";
htmldef "mapd" as "mapd";
  althtmldef "mapd" as "mapd";
  latexdef "mapd" as "{\rm mapd}";
htmldef "HVMap" as "HVMap";
  althtmldef "HVMap" as "HVMap";
  latexdef "HVMap" as "{\rm HVMap}";
/*
htmldef "eImage" as "eImage";
  althtmldef "eImage" as "eImage";
  latexdef "eImage" as "{\rm eImage}";
*/
htmldef "HDMap1" as "HDMap1";
  althtmldef "HDMap1" as "HDMap1";
  latexdef "HDMap1" as "{\rm HDMap1}";
htmldef "HDMap" as "HDMap";
  althtmldef "HDMap" as "HDMap";
  latexdef "HDMap" as "{\rm HDMap}";
htmldef "HGMap" as "HGMap";
  althtmldef "HGMap" as "HGMap";
  latexdef "HGMap" as "{\rm HGMap}";
htmldef "HLHil" as "HLHil";
  althtmldef "HLHil" as "HLHil";
  latexdef "HLHil" as "{\rm HLHil}";
/*
htmldef "*HRing" as "*HRing";
  althtmldef "*HRing" as "*HRing";
  latexdef "*HRing" as "\ast{\rm HRing}";
htmldef "hmap" as "hmap";
  althtmldef "hmap" as "hmap";
  latexdef "hmap" as "{\rm hmap}";
htmldef "gmap" as "gmap";
  althtmldef "gmap" as "gmap";
  latexdef "gmap" as "{\rm gmap}";
htmldef "mapd" as "mapd";
  althtmldef "mapd" as "mapd";
  latexdef "mapd" as "{\rm mapd}";
htmldef "GrpEndo" as "GrpEndo"; althtmldef "GrpEndo" as "GrpEndo";
htmldef "DVecAEndo" as "DVecAEndo"; althtmldef "DVecAEndo" as "DVecAEndo";
htmldef "ERing" as "ERing"; althtmldef "ERing" as "ERing";
htmldef "TPEndo" as "TPEndo"; althtmldef "TPEndo" as "TPEndo";
htmldef "DRing" as "DRing"; althtmldef "DRing" as "DRing";
htmldef "DVecA" as "DVecA"; althtmldef "DVecA" as "DVecA";
htmldef "DVIsoPre" as "DVIsoPre"; althtmldef "DVIsoPre" as "DVIsoPre";
htmldef "DVecB" as "DVecB"; althtmldef "DVecB" as "DVecB";
htmldef "DVecH" as "DVecH"; althtmldef "DVecH" as "DVecH";
htmldef "ee" as "ee"; althtmldef "ee" as "ee";
htmldef "DVIsoA" as "DVIsoA"; althtmldef "DVIsoA" as "DVIsoA";
htmldef "qtr" as "qtr"; althtmldef "qtr" as "qtr";
htmldef "DVIsoB" as "DVIsoB"; althtmldef "DVIsoB" as "DVIsoB";
htmldef "DVIsoC" as "DVIsoC"; althtmldef "DVIsoC" as "DVIsoC";
htmldef "DVIsoH" as "DVIsoH"; althtmldef "DVIsoH" as "DVIsoH";
htmldef "S_|_" as "S_|_"; althtmldef "S_|_" as "S_|_";
htmldef "Ropp" as "Ropp"; althtmldef "Ropp" as "Ropp";
htmldef "Vldual" as "Vldual"; althtmldef "Vldual" as "Vldual";
htmldef "vecdom" as "vecdom"; althtmldef "vecdom" as "vecdom";
htmldef "ker" as "ker"; althtmldef "ker" as "ker";
htmldef "mapd" as "mapd"; althtmldef "mapd" as "mapd";
htmldef "eimage" as "eimage"; althtmldef "eimage" as "eimage";
htmldef "hmap" as "hmap"; althtmldef "hmap" as "hmap";
htmldef "gmap" as "gmap"; althtmldef "gmap" as "gmap";
htmldef "HLtoHil" as "HLtoHil"; althtmldef "HLtoHil" as "HLtoHil";
*/


/* End of typesetting definition section */
$)

