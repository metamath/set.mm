$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Stefan Allan
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    sa-abvi.1 $e |- ph $.
    $( A theorem about the universal class.  Inference associated with ~ bj-abv
       (which is proved from fewer axioms).  (Contributed by Stefan Allan,
       9-Dec-2008.) $)
    sa-abvi $p |- _V = { x | ph } $=
      ( cvv weq cab df-v equid 2th abbii eqtri ) DBBEZBFABFBGLABLABHCIJK $.
  $}

  $( A partial converse to ~ 19.9t .  (Contributed by Stefan Allan,
     21-Dec-2008.)  (Revised by Mario Carneiro, 11-Dec-2016.) $)
  xfree $p |- ( A. x ( ph -> A. x ph ) <-> A. x ( E. x ph -> ph ) ) $=
    ( wal wi wnf wex nf5 nf6 bitr3i ) AABCDBCABEABFADBCABGABHI $.

  $( A partial converse to ~ 19.9t .  (Contributed by Stefan Allan,
     21-Dec-2008.) $)
  xfree2 $p |- ( A. x ( ph -> A. x ph ) <-> A. x ( -. ph -> A. x -. ph ) ) $=
    ( wal wi wex wn xfree eximal albii bitri ) AABCDBCABEADZBCAFZLBCDZBCABGKMBA
    ABHIJ $.

  $( A proof readability experiment for ~ addltmul .  (Contributed by Stefan
     Allan, 30-Oct-2010.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  addltmulALT $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( 2 < A /\ 2 < B ) )
              -> ( A + B ) < ( A x. B ) ) $=
    ( cr wcel wa c2 clt wbr c1 cmin co caddc cmul a1i syl3anc ax-1cn syl adantr
    wb wceq simpr 2re simpl 1re ltsub1 df-2 eqcomi subaddrii breq1i bitrd mpbid
    2cn anim12i an4s wi peano2rem anim1i mulgt1 ex cc recn mulsub breq2d biimpd
    jca mullidi eqcom biimpi mp1i oveq2d mulrid oveq12d readdcl remulcl syl2anc
    adantl ltaddsub2 ltadd1 bicomd sylbird 3syld mpd ) ACDZBCDZEZFAGHZFBGHZEZEZ
    IAIJKZGHZIBIJKZGHZEZABLKZABMKZGHZWCWFWDWGWNWCWFEZWKWDWGEZWMWRWFWKWCWFUAWRWF
    FIJKZWJGHZWKWRFCDZWCICDZWFXASXBWRUBNWCWFUCXCWRUDNFAIUEOXAWKSWRWTIWJGFIIULPP
    FIILKUFUGUHZUINUJUKWSWGWMWDWGUAWSWGWTWLGHZWMWSXBWDXCWGXESXBWSUBNWDWGUCXCWSU
    DNFBIUEOXEWMSWSWTIWLGXDUINUJUKUMUNWIWNIWJWLMKZGHZIWPIIMKZLKZAIMKZBIMKZLKZJK
    ZGHZWQWEWNXGUOWHWEWNXGWEWNEWJCDZWLCDZEZWNEXGWEXQWNWCXOWDXPAUPBUPUMUQWJWLURQ
    USRWEXGXNUOWHWEXGXNWEXFXMIGWEAUTDZIUTDZEZBUTDZXSEZEXFXMTWCXTWDYBWCXRXSAVAZX
    SWCPNVEWDYAXSBVAZXSWDPNVEUMAIBIVBQVCVDRWEXNWQUOWHWEXNIWPILKZWOJKZGHZWQWEYFX
    MIGWEYEXIWOXLJWEIXHWPLXHITZIXHTZWEIPVFYHYIXHIVGVHVIVJWEAXJBXKLWCAXJTZWDWCXR
    YJYCXRXJATZYJAVKYKYJXJAVGVHQQRWDBXKTZWCWDXKBTZYLWDYAYMYDBVKQYMYLXKBVGVHQVPV
    LVLVCWEYGWOILKYEGHZWQWEWOCDZXCYECDZYNYGSABVMZXCWEUDNZWEWPCDZXCYPABVNZYRWPIV
    MVOWOIYEVQOWEYNWQWEWQYNWEYOYSXCWQYNSYQYTYRWOWPIVROVSVDVTVTRWAWB $.

$( (End of Stefan Allan's mathbox.) $)
