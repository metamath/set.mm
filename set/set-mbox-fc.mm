$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Filip Cernatescu
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  I hope someone will enjoy solving (proving) the simple equations,
  inequalities, and calculations from this mathbox.  I have proved these
  problems (theorems) using the Milpgame proof assistant.  (It can be
  downloaded from ~ https://us.metamath.org/other/milpgame/milpgame.html .)

$)

  $( Practice problem 1.  Clues: ~ 5p4e9 ~ 3p2e5 ~ eqtri ~ oveq1i .
     (Contributed by Filip Cernatescu, 16-Mar-2019.)
     (Proof modification is discouraged.) $)
  problem1 $p |- ( ( 3 + 2 ) + 4 ) = 9 $=
    ( c3 c2 caddc co c4 c5 c9 3p2e5 oveq1i 5p4e9 eqtri ) ABCDZECDFECDGLFECHIJK
    $.

  $( Practice problem 2.  Clues: ~ oveq12i ~ adddiri ~ add4i ~ mulcli ~ recni
     ~ 2re ~ 3eqtri ~ 10re ~ 5re ~ 1re ~ 4re ~ eqcomi ~ 5p4e9 ~ oveq1i ~ df-3 .
     (Contributed by Filip Cernatescu, 16-Mar-2019.)  (Revised by AV,
     9-Sep-2021.)  (Proof modification is discouraged.) $)
  problem2 $p |- ( ( ( 2 x. ; 1 0 ) + 5 ) + ( ( 1 x. ; 1 0 ) + 4 ) )
          = ( ( 3 x. ; 1 0 ) + 9 ) $=
    ( c2 c1 cc0 cdc cmul co c5 caddc c4 c9 c3 2re recni 10re mulcli 5re 1re 4re
    eqcomi oveq1i add4i adddiri 5p4e9 oveq12i df-3 3eqtri ) ABCDZEFZGHFBUGEFZIH
    FHFUHUIHFZGIHFZHFABHFZUGEFZJHFKUGEFZJHFUHGUIIAUGALMZUGNMZOGPMBUGBQMZUPOIRMU
    AUJUMUKJHUMUJABUGUOUQUPUBSUCUDUMUNJHULKUGEKULUESTTUF $.

  ${
    problem3.1 $e |- A e. CC $.
    problem3.2 $e |- ( A + 3 ) = 4 $.
    $( Practice problem 3.  Clues: ~ eqcomi ~ eqtri ~ subaddrii ~ recni ~ 4re
       ~ 3re ~ 1re ~ df-4 ~ addcomi .  (Contributed by Filip Cernatescu,
       16-Mar-2019.)  (Proof modification is discouraged.) $)
    problem3 $p |- A = 1 $=
      ( c1 c4 c3 cmin co 4re recni 3re 1re caddc eqcomi subaddrii addcomi eqtri
      df-4 ) DADEFGHZASDEFDEIJZFKJZDLJEFDMHRNONEFATUABFAMHAFMHEFAUABPCQOQN $.
  $}

  ${
    problem4.1 $e |- A e. CC $.
    problem4.2 $e |- B e. CC $.
    problem4.3 $e |- ( A + B ) = 3 $.
    problem4.4 $e |- ( ( 3 x. A ) + ( 2 x. B ) ) = 7 $.
    $( Practice problem 4.  Clues: ~ pm3.2i ~ eqcomi ~ eqtri ~ subaddrii
       ~ recni ~ 7re ~ 6re ~ ax-1cn ~ df-7 ~ ax-mp ~ oveq1i ~ 3cn ~ 2cn ~ df-3
       ~ mullidi ~ subdiri ~ mp3an ~ mulcli ~ subadd23 ~ oveq2i ~ oveq12i
       ~ 3t2e6 ~ mulcomi ~ subcli ~ biimpri ~ subadd2i .  (Contributed by Filip
       Cernatescu, 16-Mar-2019.)  (Proof modification is discouraged.) $)
    problem4 $p |- ( A = 1 /\ B = 2 ) $=
      ( c1 wceq c2 c7 c6 cmin co caddc eqcomi c3 cmul 3cn 2cn eqtri ax-1cn df-7
      7re recni 6re subaddrii df-3 oveq1i mullidi subdiri mulcli subadd23 mp3an
      cc wcel 3t2e6 mulcomi oveq12i subcli oveq2i subadd2i biimpri ax-mp pm3.2i
      ) AGHBIHGAGJKLMZAVEGJKGJUCUDZKUEUDZUAJKGNMUBOUFOAKNMZJHZVEAHZVHPAQMZIBQMZ
      NMZJVHVKIAQMZLMZKNMZVMAVOKNAPILMZAQMZVOVRAVRGAQMAVQGAQPIGRSUAPIGNMZUGOZUF
      UHACUITOPIARSCUJTUHVPVKKVNLMZNMZVMVKUNUOVNUNUOKUNUOVPWBHPARCUKIASCUKVGVKV
      NKULUMVMWBVLWAVKNWAVLWAPIQMZAIQMZLMZVLWEWAWCKWDVNLUPAICSUQUROWEPALMZIQMZV
      LWGWEPAIRCSUJOWGIWFQMZVLWHWGIWFSPARCUSUQOVLWHBWFIQWFBPABRCDEUFOZUTOTTTOUT
      OTTFTVJVIJKAVFVGCVAVBVCTOZBWFIWIWFPGLMZIAGPLWJUTVSPHZWKIHZVTWMWLPGIRUASVA
      VBVCTTVD $.
  $}

  ${
    problem5.1 $e |- A e. RR $.
    problem5.2 $e |- ( ( 2 x. A ) + 3 ) < 9 $.
    $( Practice problem 5.  Clues: ~ 3brtr3i ~ mpbi ~ breqtri ~ ltaddsubi
       ~ remulcli ~ 2re ~ 3re ~ 9re ~ eqcomi ~ mvlladdi 3cn ~ 6cn ~ eqtr3i
       ~ 6p3e9 ~ addcomi ~ ltdiv1ii ~ 6re ~ nngt0i ~ 2nn ~ divcan3i ~ recni
       ~ 2cn ~ 2ne0 ~ mpbir ~ eqtri ~ mulcomi ~ 3t2e6 ~ divmuli .  (Contributed
       by Filip Cernatescu, 16-Mar-2019.)
       (Proof modification is discouraged.) $)
    problem5 $p |- A < 3 $=
      ( c2 cmul co cdiv c6 c3 clt wbr c9 caddc 2re mpbi 3cn 6cn eqcomi 2cn 2ne0
      cmin remulcli 3re 9re ltaddsubi 6p3e9 addcomi eqtr3i mvlladdi breqtri 6re
      2nn nngt0i ltdiv1ii recni divcan3i wceq mulcomi 3t2e6 eqtri divmuli mpbir
      3brtr3i ) DAEFZDGFZHDGFZAIJVDHJKVEVFJKVDLIUAFZHJVDIMFLJKVDVGJKCVDILDANBUB
      ZUCUDUEOHVGIHLPQLIHMFZHIMFLVIUFHIQPUGUHRUIRUJVDHDVHUKNDULUMUNOADABUOSTUPV
      FIUQDIEFZHUQVJIDEFHDISPURUSUTHDIQSPTVAVBVC $.
  $}

  ${
    quad3.1 $e |- X e. CC $.
    quad3.2 $e |- A e. CC $.
    quad3.3 $e |- A =/= 0 $.
    quad3.4 $e |- B e. CC $.
    quad3.5 $e |- C e. CC $.
    quad3.6 $e |- ( ( A x. ( X ^ 2 ) ) + ( ( B x. X ) + C ) ) = 0 $.
    $( Variant of quadratic equation with discriminant expanded.  (Contributed
       by Filip Cernatescu, 19-Oct-2019.) $)
    quad3 $p |- ( X = ( ( -u B + ( sqrt ` ( ( B ^ 2 ) - ( 4 x. ( A x. C ) ) )
              ) ) / ( 2 x. A ) ) \/ X = ( ( -u B - ( sqrt ` ( ( B ^ 2 ) -
              ( 4 x. ( A x. C ) ) ) ) ) / ( 2 x. A ) ) ) $=
      ( c2 cmul co cdiv caddc cmin wceq 2cn oveq2i oveq1i cexp c4 csqrt cneg wo
      cfv mulcli 2ne0 mulne0i divcli addcli sqmuli binom2i sqcli divdiri div23i
      divcan3i oveq12i eqtr2i mulcomi divcan2i divassi cc cc0 wa pm3.2i divdiv1
      wcel wne mp3an eqtri 3eqtr2i addassi eqcomi pncan3oi df-neg eqtr4i negcli
      3eqtr3i addcomi sqdivi 4cn 4ne0 divmuldivi c1 dividi eqtr3i mulm1i neg1cn
      mullidi mulassi 3eqtri 2t2e4 sqvali eqnetri negsubi subcli eqsqrtor ax-mp
      wb mpbi sqrtcl divmuli eqcom bitr3i subadd2i divneg eqeq2i 3bitri orbi12i
      ) KALMZDBXKNMZOMZLMZBKUAMZUBACLMZLMZPMZUCUFZQZXNXSUDZQZUEZDBUDZXSOMXKNMZQ
      ZDYDXSPMZXKNMZQZUEXNKUAMZXRQZYCYJXKKUAMZXMKUAMZLMYLXRYLNMZLMXRXKXMKARFUGZ
      DXLEBXKHYOKARFUHGUIZUJZUKZULYMYNYLLYMCUDZANMZXLKUAMZOMZUUAYTOMZYNYMDKUAMZ
      KDXLLMZLMZOMZUUAOMUUBDXLEYQUMUUGYTUUAOUUDBANMZDLMZOMZAUUDLMZBDLMZOMZANMZU
      UGYTUUNUUKANMZUULANMZOMUUJUUKUULAAUUDFDEUNZUGZBDHEUGZFGUOUUOUUDUUPUUIOUUD
      AUUQFGUQBDAHEFGUPURUSUUIUUFUUDOUUIDUUHLMZKUUTKNMZLMUUFUUHDBAHFGUJZEUTUUTK
      DUUHEUVBUGRUHVAUVAUUEKLUVADUUHKNMZLMUUEDUUHKEUVBRUHVBUVCXLDLUVCBAKLMZNMZX
      LBVCVHZAVCVHZAVDVIZVEKVCVHZKVDVIZVEUVCUVEQHUVGUVHFGVFUVIUVJRUHVFBAKVGVJUV
      DXKBNAKFRUTSVKSVKSVLSUUMYSANUUMUUKUULCOMOMZCPMZYSUVLUUMCOMZCPMUUMUVKUVMCP
      UVMUVKUUKUULCUURUUSIVMVNTUUMCUUKUULUURUUSUKIVOUSUVLVDCPMYSUVKVDCPJTCVPVQV
      KTVSTVKYTUUAYSACIVRZFGUJZXLYQUNVTUUCXOYLNMZXQUDZYLNMZOMXOUVQOMZYLNMYNUUAU
      VPYTUVROBXKHYOYPWAUBALMZUVTNMZYTLMZUVTYSLMZUVTALMZNMYTUVRUVTUVTYSAUBAWBFU
      GZUWEUVNFUBAWBFWCGUIZGWDWEYTLMUWBYTWEUWAYTLUWAWEUVTUWEUWFWFVNTYTUVOWJWGUW
      CUVQUWDYLNUWCWEUDZUVTCLMZLMZUWGXQLMUVQUWCUVTUWGLMZCLMZUWGUVTLMZCLMUWIUWCU
      VTUWGCLMZLMUWKYSUWMUVTLUWMYSCIWHVNSUVTUWGCUWEWIIWKVQUWJUWLCLUVTUWGUWEWIUT
      TUWGUVTCWIUWEIWKWLUWHXQUWGLUBACWBFIWKSXQUBXPWBACFIUGUGZWHWLUWDXKXKLMZYLUW
      DKXKLMZALMZXKKLMZALMUWOUWDKKLMZALMZALMUWQUVTUWTALUBUWSALUWSUBWMVNTTUWTUWP
      ALKKARRFWKTVKUWPUWRALKXKRYOUTTXKKAYORFWKWLXKYOWNZVQURVSURXOUVQYLBHUNZXQUW
      NVRXKYOUNZYLUWOVDUXAXKXKYOYOYPYPUIWOZUOUVSXRYLNXOXQUXBUWNWPTVLWLSXRYLXOXQ
      UXBUWNWQZUXCUXDVAWLXNVCVHZXRVCVHZVEYKYCWTUXFUXGXKXMYOYRUGUXEVFXNXRWRWSXAX
      TYFYBYIXTXMXSXKNMZQZDUXHXLPMZQZYFXTUXHXMQUXIXSXKXMUXGXSVCVHUXEXRXBWSZYOYR
      YPXCUXHXMXDXEUXIUXJDQUXKUXHXLDXSXKUXLYOYPUJZYQEXFUXJDXDXEUXJYEDUXJYDXKNMZ
      UXHOMZYEUXHXLUDZOMUXHUXNOMUXJUXOUXPUXNUXHOUVFXKVCVHXKVDVIUXPUXNQHYOYPBXKX
      GVJZSUXHXLUXMYQWPUXHUXNUXMYDXKBHVRZYOYPUJZVTVSYDXSXKUXRUXLYOYPUOVQXHXIYBX
      MYAXKNMZQZDUXTXLPMZQZYIYBUXTXMQUYAYAXKXMXSUXLVRZYOYRYPXCUXTXMXDXEUYAUYBDQ
      UYCUXTXLDYAXKUYDYOYPUJZYQEXFUYBDXDXEUYBYHDUYBUXNUXTOMZYDYAOMZXKNMYHUXTUXP
      OMUXTUXNOMUYBUYFUXPUXNUXTOUXQSUXTXLUYEYQWPUXTUXNUYEUXSVTVSYDYAXKUXRUYDYOY
      PUOUYGYGXKNYDXSUXRUXLWPTVLXHXIXJXA $.
  $}

$( (End of Filip Cernatescu's mathbox.) $)
