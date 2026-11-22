import HeadComplexity.Atoms.CoordinateZeroCubeSplit

set_option linter.style.header false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-! Complete kernel enumeration of the zero set at the sixteen-bit base point.
This certifies finite data, not an asymptotic head-complexity theorem. -/
namespace HeadComplexity.CoordinateZeroFiber

def packedHalves : Fin 4 → Fin 3 → ℕ := ![
  ![19262969424550673393355247159062899127762530100016015519958063194474497533969286810324458373597391642475386840541309327817208438189502602808149435541937966456908429076068094516287407394289588855563598553532383933968904069224677655738450803573997093825288952358923996638624499148639878911721380531982970671150940759740773902155636447459302512012388882593470265315676486815196544620229380995778917503418376197477216710620980846225726815167697957261176760944308406412751067554182642757781496534847355959583999512166289977450281257908655343208268885571990920637603392909105270919664113051365267423393756543160948237828480, 19135746809070620608373946320705177247358069905738469001659718930785221200639234190717817776731914097392936269823044557056125054199987935568528411417552894883444574697265611326418419116715314122250506108958407433955506927411761356766085316205703303424112240683886213973174422176979232213293224237429104789812313022631395992492226751639706352104054402135112449587170232506148904956155955146602538673191572123265188461275421943302188493932546302138039697190421008300593722661826063175363819456455469547372831662091207914002272129247747797143381717038722359829605579918852169245041455443455475364273249181098679680008832, 18120895633892952999597990231217418167377680043116298775930181980462149350310619172457751395627285370702270972266098547227207067704393405819809536671613660866311058444364494699461086764009860656132562351404321904338255414798820241847949496387746051905429067580416990502230735585862456358970726543404799632028994922660152862198705227524317230969236817877372334203272328863200947525048015933410033865459322115850871677234022753896637234476911111681106957607670978680903646877908933080336953316939470418755578372646347532713146170081334573043280974695037982725461106407509697335372526942226482823178646973023262188078208],
  ![18501586897425854858099619097192772236694710862324378054380578557572468751508828550283025949988416687234031352815727186817795511817831368350193159189475765103029353824376264743064904063429491678923821364523611020482911941539078277712494713183165600863795533938834279711042132604125401174585517202441324193048623625917401224923692600621284729563083773197750873124508802803792264054198342298126644299509842526561671810067483317633661226477000226749564960586977464511564539983712311143595571951969881809842448661004593660790857095579170521632415625919549969318108438005782900835544695893738301921081008311465429157708672, 18502575083000467329252280152664301668552169950319988909890442109925415158021342130432432191080253952643902655517303588223727267872015708717425450570110040195870408392996014591059553549460368968318856594374091846162524443934211034936473755978430504706483477988820369965512971272795567618666268066767020678325772881435453980505673061148276061973438772366175163192847131818407109255196775266731014867907624254350415651190343746554477573656964112932423358871166720906145502282313955841700781499194092214018212374541218387240572748149088860487881712303249910915973732840709899718591783267319768927377239201059379058147712, 18629304572695271944805566337071296729381873841210811107783491163519323626703727569996051857248056899196669579993601292492221909031054780607407421368689575045483430491495648875144164398318212888443261696853433535891866773886795170655736761500861859868919539511837474466001011308791704923565479986491746661188710263525816075422612559494661392033591585911849933939944552140362623032464675692153834769995924247444462645064566102064968025363138159278955807179440142208407673477196677615110134869816404454539418032097194745380949064799359616416787115681333315106360529803366299500859062536698795440025768204551652523606400],
  ![13687697631197651273489368473745264862561411209825136415907572529396516217450505723797638613807007193875787593969157162799211991204412598940499746521544547372592575683189394828947102519834725231567720228604952810739013314620190469487385194956266655691129107247469740376012165372189973121105143718083864776123328968186656969938716312496743886243427732083432479360373640575673215442540987955610395014001513480688699492660126831794781131040291968170952414095057684344281706149177419431839867543226418710047406399666150231851853425756345540443343089416305425442769131872757501782144456603520043179715916022037241925697408, 13686717180724773649150807275778204117884113313218198211931968755750117903014040653525909154611462627375909393230740581696985804670750275218621766441993648391721014062904842212743314289345613580322242190358748483083008445406430035808128727103918044077461006977291806027255204595034156283307160015174282556291898456378208036109839863517078959655375411231368139691900537178261448438640753052657189827478210532230599209880173364805335957434830260067570429648745468726978295752374690622692956634382571441077247006710090598316961194745049156828472287976800475621595500697829328310594515041544370566470351320762614451831168, 14956514447779037253206138000468749149378497629012644224905309648152114601681954005118017357210311661588663910285273732193312009699769066617277243659267022061158225592106241854393334083108611654953804853473686532155104679674850296924280848447174356926851061890573577583269127920912607779511214442363908944367322998567002693617548600779471291003368581678197158014723005126637559178366099711266404461134515177944353961005021085399419647779227815886184881634521238836871086391790955814659815076323379540646091709424360340068666034843871253348832582061548760842147848268230693298793199399129487106996961315769219823795328],
  ![14197094755397538235236769455509592137471444054079744139495817037114808936778082977651042583121203823521765534289516385204885484946029809201002185892882257580265374119041040204999282224167650449133263602666888208771474991651756738745781637541178830887350185973297967862291806244656431416934004870046860610358561748613463606282068299276861898982396203398430111053314209164129065150292423208791411935789947367494579992480744395534299185189604754290462206056212506212947126370321617864900727111866225277010652226009063079040743966787461687758015886430454867662975177946607898438517659593749205658538871889117493288008320, 13055514090702110465520363361175918715612970342402267179648159260889656581345125054680391599816781115927418081854616862918351093007074783127064465057392606179509397377807378674371407642448803828897688334651028935704369096770947174419718924483850198950084504777711959285559879891911905008787740613927195202194560322493377806074241206669948133029302273924458040981636701941381409639315018492139029972010066600241281536342819403142349001432178189811832734007439299177406057886480759028618780258642974398280343189361808479573172854981068993237939802951119589891322891194666080970763515577856812258096951092010131017006208, 14196110437418054301103145999338517075127438237223877902492748133282509443736978030935119742340842899300358323716626704382191492413955195052417458213121461347124296799190202241522094929573988294635600342094616701024847625150998578643020612256583670857900656421716011339665975842430156586567099196684696564180596748688782008930930854117306505067398722889467375002283782344520543251279654679061704554259836726303700093788614107840096265098875314151912265021160768502136717233007027395703494569645781660686887881678566935218334134024114951474857808220032974777822098164519515126738076037317818971178314136251872369933440]]

def halfAt (g : Fin 4) (h : Fin 3) (j : Fin 256) : ℤ :=
  (((packedHalves g h >>> (8 * j.val)) % 256 : ℕ) : ℤ) - 128

theorem half_low_den : ∀ h j,
    halfAt 0 h j = lowDot (denominatorSlopes h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

theorem half_high_den : ∀ h j,
    halfAt 1 h j = highDot (denominatorSlopes h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

theorem half_low_num : ∀ h j,
    halfAt 2 h j = lowDot (numeratorScaledSlopes h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

theorem half_high_num : ∀ h j,
    halfAt 3 h j = highDot (numeratorScaledSlopes h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

def cachedDen (h : Fin 3) (k j : Fin 256) : ℤ :=
  1 + halfAt 0 h j + halfAt 1 h k

def cachedNum (h : Fin 3) (k j : Fin 256) : ℤ :=
  halfAt 2 h j + halfAt 3 h k

theorem cachedDen_eq (h : Fin 3) (k j : Fin 256) :
    cachedDen h k j = den h (256 * k.val + j.val) := by
  rw [den_split]
  simp only [cachedDen, half_low_den, half_high_den]

theorem cachedNum_eq (h : Fin 3) (k j : Fin 256) :
    cachedNum h k j = num h (256 * k.val + j.val) := by
  rw [num_split]
  simp only [cachedNum, half_low_num, half_high_num]

def cachedScore (k j : Fin 256) : ℤ :=
  3 * cachedDen 0 k j * cachedDen 1 k j * cachedDen 2 k j +
    cachedNum 0 k j * cachedDen 1 k j * cachedDen 2 k j +
    cachedNum 1 k j * cachedDen 0 k j * cachedDen 2 k j +
    cachedNum 2 k j * cachedDen 0 k j * cachedDen 1 k j

theorem cachedScore_eq (k j : Fin 256) :
    cachedScore k j = clearedScore (256 * k.val + j.val) := by
  simp only [cachedScore, clearedScore, cachedDen_eq, cachedNum_eq]

def zeroVertexList : List ℕ := [
4, 305, 318, 335, 997, 1359, 1429, 1445, 1456, 1525, 3422, 3479, 3495, 3575, 3905, 4423, 7510, 8311, 8477, 8590, 8968, 9032, 9303, 10591, 12560, 12710, 13798, 14674, 16389, 16765, 17247, 17520, 17755, 18548, 19445, 19476, 19492, 19572, 19720, 20757, 20773, 20853, 21335, 22789, 22807, 22823, 22903, 23847, 24768, 24891, 25032, 25089, 25435, 25653, 25865, 26625, 27332, 27703, 28429, 28742, 31073, 31111, 31538, 33219, 34772, 35298, 36306, 41247, 41472, 41802, 43044, 44851, 45330, 47362, 47894, 49204, 49553, 49569, 49649, 50131, 50638, 51466, 51585, 51603, 51619, 51699, 53009, 54726, 55044, 55554, 55559, 57347, 57538, 57689, 57723, 57834, 58232, 58635, 59558, 60000, 60434, 60517, 60948, 61811, 64336, 64452]

def extraZeroVertices : Finset ℕ := {
51619, 51699, 58635, 59558, 60434, 60517, 60948, 61811, 64336, 64452}

theorem zeroVertexList_length : zeroVertexList.length = 106 := by decide +kernel
theorem zeroVertexList_nodup : zeroVertexList.Nodup := by decide +kernel

theorem zeroVertexList_decomposition :
    zeroVertexList.toFinset = Finset.univ.image indices ∪ extraZeroVertices := by
  decide +kernel

private theorem zero_block_0 : ∀ j : Fin 256,
    (cachedScore 0 j = 0 ↔
      (256 * 0 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_1 : ∀ j : Fin 256,
    (cachedScore 1 j = 0 ↔
      (256 * 1 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_2 : ∀ j : Fin 256,
    (cachedScore 2 j = 0 ↔
      (256 * 2 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_3 : ∀ j : Fin 256,
    (cachedScore 3 j = 0 ↔
      (256 * 3 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_4 : ∀ j : Fin 256,
    (cachedScore 4 j = 0 ↔
      (256 * 4 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_5 : ∀ j : Fin 256,
    (cachedScore 5 j = 0 ↔
      (256 * 5 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_6 : ∀ j : Fin 256,
    (cachedScore 6 j = 0 ↔
      (256 * 6 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_7 : ∀ j : Fin 256,
    (cachedScore 7 j = 0 ↔
      (256 * 7 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_8 : ∀ j : Fin 256,
    (cachedScore 8 j = 0 ↔
      (256 * 8 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_9 : ∀ j : Fin 256,
    (cachedScore 9 j = 0 ↔
      (256 * 9 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_10 : ∀ j : Fin 256,
    (cachedScore 10 j = 0 ↔
      (256 * 10 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_11 : ∀ j : Fin 256,
    (cachedScore 11 j = 0 ↔
      (256 * 11 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_12 : ∀ j : Fin 256,
    (cachedScore 12 j = 0 ↔
      (256 * 12 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_13 : ∀ j : Fin 256,
    (cachedScore 13 j = 0 ↔
      (256 * 13 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_14 : ∀ j : Fin 256,
    (cachedScore 14 j = 0 ↔
      (256 * 14 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_15 : ∀ j : Fin 256,
    (cachedScore 15 j = 0 ↔
      (256 * 15 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_16 : ∀ j : Fin 256,
    (cachedScore 16 j = 0 ↔
      (256 * 16 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_17 : ∀ j : Fin 256,
    (cachedScore 17 j = 0 ↔
      (256 * 17 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_18 : ∀ j : Fin 256,
    (cachedScore 18 j = 0 ↔
      (256 * 18 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_19 : ∀ j : Fin 256,
    (cachedScore 19 j = 0 ↔
      (256 * 19 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_20 : ∀ j : Fin 256,
    (cachedScore 20 j = 0 ↔
      (256 * 20 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_21 : ∀ j : Fin 256,
    (cachedScore 21 j = 0 ↔
      (256 * 21 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_22 : ∀ j : Fin 256,
    (cachedScore 22 j = 0 ↔
      (256 * 22 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_23 : ∀ j : Fin 256,
    (cachedScore 23 j = 0 ↔
      (256 * 23 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_24 : ∀ j : Fin 256,
    (cachedScore 24 j = 0 ↔
      (256 * 24 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_25 : ∀ j : Fin 256,
    (cachedScore 25 j = 0 ↔
      (256 * 25 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_26 : ∀ j : Fin 256,
    (cachedScore 26 j = 0 ↔
      (256 * 26 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_27 : ∀ j : Fin 256,
    (cachedScore 27 j = 0 ↔
      (256 * 27 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_28 : ∀ j : Fin 256,
    (cachedScore 28 j = 0 ↔
      (256 * 28 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_29 : ∀ j : Fin 256,
    (cachedScore 29 j = 0 ↔
      (256 * 29 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_30 : ∀ j : Fin 256,
    (cachedScore 30 j = 0 ↔
      (256 * 30 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_31 : ∀ j : Fin 256,
    (cachedScore 31 j = 0 ↔
      (256 * 31 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_32 : ∀ j : Fin 256,
    (cachedScore 32 j = 0 ↔
      (256 * 32 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_33 : ∀ j : Fin 256,
    (cachedScore 33 j = 0 ↔
      (256 * 33 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_34 : ∀ j : Fin 256,
    (cachedScore 34 j = 0 ↔
      (256 * 34 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_35 : ∀ j : Fin 256,
    (cachedScore 35 j = 0 ↔
      (256 * 35 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_36 : ∀ j : Fin 256,
    (cachedScore 36 j = 0 ↔
      (256 * 36 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_37 : ∀ j : Fin 256,
    (cachedScore 37 j = 0 ↔
      (256 * 37 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_38 : ∀ j : Fin 256,
    (cachedScore 38 j = 0 ↔
      (256 * 38 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_39 : ∀ j : Fin 256,
    (cachedScore 39 j = 0 ↔
      (256 * 39 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_40 : ∀ j : Fin 256,
    (cachedScore 40 j = 0 ↔
      (256 * 40 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_41 : ∀ j : Fin 256,
    (cachedScore 41 j = 0 ↔
      (256 * 41 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_42 : ∀ j : Fin 256,
    (cachedScore 42 j = 0 ↔
      (256 * 42 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_43 : ∀ j : Fin 256,
    (cachedScore 43 j = 0 ↔
      (256 * 43 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_44 : ∀ j : Fin 256,
    (cachedScore 44 j = 0 ↔
      (256 * 44 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_45 : ∀ j : Fin 256,
    (cachedScore 45 j = 0 ↔
      (256 * 45 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_46 : ∀ j : Fin 256,
    (cachedScore 46 j = 0 ↔
      (256 * 46 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_47 : ∀ j : Fin 256,
    (cachedScore 47 j = 0 ↔
      (256 * 47 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_48 : ∀ j : Fin 256,
    (cachedScore 48 j = 0 ↔
      (256 * 48 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_49 : ∀ j : Fin 256,
    (cachedScore 49 j = 0 ↔
      (256 * 49 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_50 : ∀ j : Fin 256,
    (cachedScore 50 j = 0 ↔
      (256 * 50 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_51 : ∀ j : Fin 256,
    (cachedScore 51 j = 0 ↔
      (256 * 51 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_52 : ∀ j : Fin 256,
    (cachedScore 52 j = 0 ↔
      (256 * 52 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_53 : ∀ j : Fin 256,
    (cachedScore 53 j = 0 ↔
      (256 * 53 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_54 : ∀ j : Fin 256,
    (cachedScore 54 j = 0 ↔
      (256 * 54 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_55 : ∀ j : Fin 256,
    (cachedScore 55 j = 0 ↔
      (256 * 55 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_56 : ∀ j : Fin 256,
    (cachedScore 56 j = 0 ↔
      (256 * 56 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_57 : ∀ j : Fin 256,
    (cachedScore 57 j = 0 ↔
      (256 * 57 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_58 : ∀ j : Fin 256,
    (cachedScore 58 j = 0 ↔
      (256 * 58 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_59 : ∀ j : Fin 256,
    (cachedScore 59 j = 0 ↔
      (256 * 59 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_60 : ∀ j : Fin 256,
    (cachedScore 60 j = 0 ↔
      (256 * 60 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_61 : ∀ j : Fin 256,
    (cachedScore 61 j = 0 ↔
      (256 * 61 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_62 : ∀ j : Fin 256,
    (cachedScore 62 j = 0 ↔
      (256 * 62 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_63 : ∀ j : Fin 256,
    (cachedScore 63 j = 0 ↔
      (256 * 63 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_64 : ∀ j : Fin 256,
    (cachedScore 64 j = 0 ↔
      (256 * 64 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_65 : ∀ j : Fin 256,
    (cachedScore 65 j = 0 ↔
      (256 * 65 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_66 : ∀ j : Fin 256,
    (cachedScore 66 j = 0 ↔
      (256 * 66 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_67 : ∀ j : Fin 256,
    (cachedScore 67 j = 0 ↔
      (256 * 67 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_68 : ∀ j : Fin 256,
    (cachedScore 68 j = 0 ↔
      (256 * 68 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_69 : ∀ j : Fin 256,
    (cachedScore 69 j = 0 ↔
      (256 * 69 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_70 : ∀ j : Fin 256,
    (cachedScore 70 j = 0 ↔
      (256 * 70 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_71 : ∀ j : Fin 256,
    (cachedScore 71 j = 0 ↔
      (256 * 71 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_72 : ∀ j : Fin 256,
    (cachedScore 72 j = 0 ↔
      (256 * 72 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_73 : ∀ j : Fin 256,
    (cachedScore 73 j = 0 ↔
      (256 * 73 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_74 : ∀ j : Fin 256,
    (cachedScore 74 j = 0 ↔
      (256 * 74 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_75 : ∀ j : Fin 256,
    (cachedScore 75 j = 0 ↔
      (256 * 75 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_76 : ∀ j : Fin 256,
    (cachedScore 76 j = 0 ↔
      (256 * 76 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_77 : ∀ j : Fin 256,
    (cachedScore 77 j = 0 ↔
      (256 * 77 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_78 : ∀ j : Fin 256,
    (cachedScore 78 j = 0 ↔
      (256 * 78 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_79 : ∀ j : Fin 256,
    (cachedScore 79 j = 0 ↔
      (256 * 79 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_80 : ∀ j : Fin 256,
    (cachedScore 80 j = 0 ↔
      (256 * 80 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_81 : ∀ j : Fin 256,
    (cachedScore 81 j = 0 ↔
      (256 * 81 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_82 : ∀ j : Fin 256,
    (cachedScore 82 j = 0 ↔
      (256 * 82 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_83 : ∀ j : Fin 256,
    (cachedScore 83 j = 0 ↔
      (256 * 83 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_84 : ∀ j : Fin 256,
    (cachedScore 84 j = 0 ↔
      (256 * 84 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_85 : ∀ j : Fin 256,
    (cachedScore 85 j = 0 ↔
      (256 * 85 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_86 : ∀ j : Fin 256,
    (cachedScore 86 j = 0 ↔
      (256 * 86 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_87 : ∀ j : Fin 256,
    (cachedScore 87 j = 0 ↔
      (256 * 87 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_88 : ∀ j : Fin 256,
    (cachedScore 88 j = 0 ↔
      (256 * 88 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_89 : ∀ j : Fin 256,
    (cachedScore 89 j = 0 ↔
      (256 * 89 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_90 : ∀ j : Fin 256,
    (cachedScore 90 j = 0 ↔
      (256 * 90 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_91 : ∀ j : Fin 256,
    (cachedScore 91 j = 0 ↔
      (256 * 91 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_92 : ∀ j : Fin 256,
    (cachedScore 92 j = 0 ↔
      (256 * 92 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_93 : ∀ j : Fin 256,
    (cachedScore 93 j = 0 ↔
      (256 * 93 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_94 : ∀ j : Fin 256,
    (cachedScore 94 j = 0 ↔
      (256 * 94 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_95 : ∀ j : Fin 256,
    (cachedScore 95 j = 0 ↔
      (256 * 95 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_96 : ∀ j : Fin 256,
    (cachedScore 96 j = 0 ↔
      (256 * 96 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_97 : ∀ j : Fin 256,
    (cachedScore 97 j = 0 ↔
      (256 * 97 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_98 : ∀ j : Fin 256,
    (cachedScore 98 j = 0 ↔
      (256 * 98 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_99 : ∀ j : Fin 256,
    (cachedScore 99 j = 0 ↔
      (256 * 99 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_100 : ∀ j : Fin 256,
    (cachedScore 100 j = 0 ↔
      (256 * 100 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_101 : ∀ j : Fin 256,
    (cachedScore 101 j = 0 ↔
      (256 * 101 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_102 : ∀ j : Fin 256,
    (cachedScore 102 j = 0 ↔
      (256 * 102 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_103 : ∀ j : Fin 256,
    (cachedScore 103 j = 0 ↔
      (256 * 103 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_104 : ∀ j : Fin 256,
    (cachedScore 104 j = 0 ↔
      (256 * 104 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_105 : ∀ j : Fin 256,
    (cachedScore 105 j = 0 ↔
      (256 * 105 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_106 : ∀ j : Fin 256,
    (cachedScore 106 j = 0 ↔
      (256 * 106 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_107 : ∀ j : Fin 256,
    (cachedScore 107 j = 0 ↔
      (256 * 107 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_108 : ∀ j : Fin 256,
    (cachedScore 108 j = 0 ↔
      (256 * 108 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_109 : ∀ j : Fin 256,
    (cachedScore 109 j = 0 ↔
      (256 * 109 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_110 : ∀ j : Fin 256,
    (cachedScore 110 j = 0 ↔
      (256 * 110 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_111 : ∀ j : Fin 256,
    (cachedScore 111 j = 0 ↔
      (256 * 111 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_112 : ∀ j : Fin 256,
    (cachedScore 112 j = 0 ↔
      (256 * 112 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_113 : ∀ j : Fin 256,
    (cachedScore 113 j = 0 ↔
      (256 * 113 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_114 : ∀ j : Fin 256,
    (cachedScore 114 j = 0 ↔
      (256 * 114 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_115 : ∀ j : Fin 256,
    (cachedScore 115 j = 0 ↔
      (256 * 115 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_116 : ∀ j : Fin 256,
    (cachedScore 116 j = 0 ↔
      (256 * 116 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_117 : ∀ j : Fin 256,
    (cachedScore 117 j = 0 ↔
      (256 * 117 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_118 : ∀ j : Fin 256,
    (cachedScore 118 j = 0 ↔
      (256 * 118 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_119 : ∀ j : Fin 256,
    (cachedScore 119 j = 0 ↔
      (256 * 119 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_120 : ∀ j : Fin 256,
    (cachedScore 120 j = 0 ↔
      (256 * 120 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_121 : ∀ j : Fin 256,
    (cachedScore 121 j = 0 ↔
      (256 * 121 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_122 : ∀ j : Fin 256,
    (cachedScore 122 j = 0 ↔
      (256 * 122 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_123 : ∀ j : Fin 256,
    (cachedScore 123 j = 0 ↔
      (256 * 123 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_124 : ∀ j : Fin 256,
    (cachedScore 124 j = 0 ↔
      (256 * 124 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_125 : ∀ j : Fin 256,
    (cachedScore 125 j = 0 ↔
      (256 * 125 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_126 : ∀ j : Fin 256,
    (cachedScore 126 j = 0 ↔
      (256 * 126 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_127 : ∀ j : Fin 256,
    (cachedScore 127 j = 0 ↔
      (256 * 127 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_128 : ∀ j : Fin 256,
    (cachedScore 128 j = 0 ↔
      (256 * 128 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_129 : ∀ j : Fin 256,
    (cachedScore 129 j = 0 ↔
      (256 * 129 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_130 : ∀ j : Fin 256,
    (cachedScore 130 j = 0 ↔
      (256 * 130 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_131 : ∀ j : Fin 256,
    (cachedScore 131 j = 0 ↔
      (256 * 131 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_132 : ∀ j : Fin 256,
    (cachedScore 132 j = 0 ↔
      (256 * 132 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_133 : ∀ j : Fin 256,
    (cachedScore 133 j = 0 ↔
      (256 * 133 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_134 : ∀ j : Fin 256,
    (cachedScore 134 j = 0 ↔
      (256 * 134 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_135 : ∀ j : Fin 256,
    (cachedScore 135 j = 0 ↔
      (256 * 135 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_136 : ∀ j : Fin 256,
    (cachedScore 136 j = 0 ↔
      (256 * 136 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_137 : ∀ j : Fin 256,
    (cachedScore 137 j = 0 ↔
      (256 * 137 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_138 : ∀ j : Fin 256,
    (cachedScore 138 j = 0 ↔
      (256 * 138 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_139 : ∀ j : Fin 256,
    (cachedScore 139 j = 0 ↔
      (256 * 139 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_140 : ∀ j : Fin 256,
    (cachedScore 140 j = 0 ↔
      (256 * 140 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_141 : ∀ j : Fin 256,
    (cachedScore 141 j = 0 ↔
      (256 * 141 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_142 : ∀ j : Fin 256,
    (cachedScore 142 j = 0 ↔
      (256 * 142 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_143 : ∀ j : Fin 256,
    (cachedScore 143 j = 0 ↔
      (256 * 143 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_144 : ∀ j : Fin 256,
    (cachedScore 144 j = 0 ↔
      (256 * 144 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_145 : ∀ j : Fin 256,
    (cachedScore 145 j = 0 ↔
      (256 * 145 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_146 : ∀ j : Fin 256,
    (cachedScore 146 j = 0 ↔
      (256 * 146 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_147 : ∀ j : Fin 256,
    (cachedScore 147 j = 0 ↔
      (256 * 147 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_148 : ∀ j : Fin 256,
    (cachedScore 148 j = 0 ↔
      (256 * 148 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_149 : ∀ j : Fin 256,
    (cachedScore 149 j = 0 ↔
      (256 * 149 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_150 : ∀ j : Fin 256,
    (cachedScore 150 j = 0 ↔
      (256 * 150 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_151 : ∀ j : Fin 256,
    (cachedScore 151 j = 0 ↔
      (256 * 151 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_152 : ∀ j : Fin 256,
    (cachedScore 152 j = 0 ↔
      (256 * 152 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_153 : ∀ j : Fin 256,
    (cachedScore 153 j = 0 ↔
      (256 * 153 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_154 : ∀ j : Fin 256,
    (cachedScore 154 j = 0 ↔
      (256 * 154 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_155 : ∀ j : Fin 256,
    (cachedScore 155 j = 0 ↔
      (256 * 155 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_156 : ∀ j : Fin 256,
    (cachedScore 156 j = 0 ↔
      (256 * 156 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_157 : ∀ j : Fin 256,
    (cachedScore 157 j = 0 ↔
      (256 * 157 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_158 : ∀ j : Fin 256,
    (cachedScore 158 j = 0 ↔
      (256 * 158 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_159 : ∀ j : Fin 256,
    (cachedScore 159 j = 0 ↔
      (256 * 159 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_160 : ∀ j : Fin 256,
    (cachedScore 160 j = 0 ↔
      (256 * 160 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_161 : ∀ j : Fin 256,
    (cachedScore 161 j = 0 ↔
      (256 * 161 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_162 : ∀ j : Fin 256,
    (cachedScore 162 j = 0 ↔
      (256 * 162 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_163 : ∀ j : Fin 256,
    (cachedScore 163 j = 0 ↔
      (256 * 163 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_164 : ∀ j : Fin 256,
    (cachedScore 164 j = 0 ↔
      (256 * 164 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_165 : ∀ j : Fin 256,
    (cachedScore 165 j = 0 ↔
      (256 * 165 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_166 : ∀ j : Fin 256,
    (cachedScore 166 j = 0 ↔
      (256 * 166 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_167 : ∀ j : Fin 256,
    (cachedScore 167 j = 0 ↔
      (256 * 167 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_168 : ∀ j : Fin 256,
    (cachedScore 168 j = 0 ↔
      (256 * 168 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_169 : ∀ j : Fin 256,
    (cachedScore 169 j = 0 ↔
      (256 * 169 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_170 : ∀ j : Fin 256,
    (cachedScore 170 j = 0 ↔
      (256 * 170 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_171 : ∀ j : Fin 256,
    (cachedScore 171 j = 0 ↔
      (256 * 171 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_172 : ∀ j : Fin 256,
    (cachedScore 172 j = 0 ↔
      (256 * 172 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_173 : ∀ j : Fin 256,
    (cachedScore 173 j = 0 ↔
      (256 * 173 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_174 : ∀ j : Fin 256,
    (cachedScore 174 j = 0 ↔
      (256 * 174 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_175 : ∀ j : Fin 256,
    (cachedScore 175 j = 0 ↔
      (256 * 175 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_176 : ∀ j : Fin 256,
    (cachedScore 176 j = 0 ↔
      (256 * 176 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_177 : ∀ j : Fin 256,
    (cachedScore 177 j = 0 ↔
      (256 * 177 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_178 : ∀ j : Fin 256,
    (cachedScore 178 j = 0 ↔
      (256 * 178 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_179 : ∀ j : Fin 256,
    (cachedScore 179 j = 0 ↔
      (256 * 179 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_180 : ∀ j : Fin 256,
    (cachedScore 180 j = 0 ↔
      (256 * 180 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_181 : ∀ j : Fin 256,
    (cachedScore 181 j = 0 ↔
      (256 * 181 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_182 : ∀ j : Fin 256,
    (cachedScore 182 j = 0 ↔
      (256 * 182 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_183 : ∀ j : Fin 256,
    (cachedScore 183 j = 0 ↔
      (256 * 183 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_184 : ∀ j : Fin 256,
    (cachedScore 184 j = 0 ↔
      (256 * 184 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_185 : ∀ j : Fin 256,
    (cachedScore 185 j = 0 ↔
      (256 * 185 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_186 : ∀ j : Fin 256,
    (cachedScore 186 j = 0 ↔
      (256 * 186 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_187 : ∀ j : Fin 256,
    (cachedScore 187 j = 0 ↔
      (256 * 187 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_188 : ∀ j : Fin 256,
    (cachedScore 188 j = 0 ↔
      (256 * 188 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_189 : ∀ j : Fin 256,
    (cachedScore 189 j = 0 ↔
      (256 * 189 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_190 : ∀ j : Fin 256,
    (cachedScore 190 j = 0 ↔
      (256 * 190 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_191 : ∀ j : Fin 256,
    (cachedScore 191 j = 0 ↔
      (256 * 191 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_192 : ∀ j : Fin 256,
    (cachedScore 192 j = 0 ↔
      (256 * 192 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_193 : ∀ j : Fin 256,
    (cachedScore 193 j = 0 ↔
      (256 * 193 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_194 : ∀ j : Fin 256,
    (cachedScore 194 j = 0 ↔
      (256 * 194 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_195 : ∀ j : Fin 256,
    (cachedScore 195 j = 0 ↔
      (256 * 195 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_196 : ∀ j : Fin 256,
    (cachedScore 196 j = 0 ↔
      (256 * 196 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_197 : ∀ j : Fin 256,
    (cachedScore 197 j = 0 ↔
      (256 * 197 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_198 : ∀ j : Fin 256,
    (cachedScore 198 j = 0 ↔
      (256 * 198 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_199 : ∀ j : Fin 256,
    (cachedScore 199 j = 0 ↔
      (256 * 199 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_200 : ∀ j : Fin 256,
    (cachedScore 200 j = 0 ↔
      (256 * 200 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_201 : ∀ j : Fin 256,
    (cachedScore 201 j = 0 ↔
      (256 * 201 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_202 : ∀ j : Fin 256,
    (cachedScore 202 j = 0 ↔
      (256 * 202 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_203 : ∀ j : Fin 256,
    (cachedScore 203 j = 0 ↔
      (256 * 203 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_204 : ∀ j : Fin 256,
    (cachedScore 204 j = 0 ↔
      (256 * 204 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_205 : ∀ j : Fin 256,
    (cachedScore 205 j = 0 ↔
      (256 * 205 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_206 : ∀ j : Fin 256,
    (cachedScore 206 j = 0 ↔
      (256 * 206 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_207 : ∀ j : Fin 256,
    (cachedScore 207 j = 0 ↔
      (256 * 207 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_208 : ∀ j : Fin 256,
    (cachedScore 208 j = 0 ↔
      (256 * 208 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_209 : ∀ j : Fin 256,
    (cachedScore 209 j = 0 ↔
      (256 * 209 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_210 : ∀ j : Fin 256,
    (cachedScore 210 j = 0 ↔
      (256 * 210 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_211 : ∀ j : Fin 256,
    (cachedScore 211 j = 0 ↔
      (256 * 211 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_212 : ∀ j : Fin 256,
    (cachedScore 212 j = 0 ↔
      (256 * 212 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_213 : ∀ j : Fin 256,
    (cachedScore 213 j = 0 ↔
      (256 * 213 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_214 : ∀ j : Fin 256,
    (cachedScore 214 j = 0 ↔
      (256 * 214 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_215 : ∀ j : Fin 256,
    (cachedScore 215 j = 0 ↔
      (256 * 215 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_216 : ∀ j : Fin 256,
    (cachedScore 216 j = 0 ↔
      (256 * 216 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_217 : ∀ j : Fin 256,
    (cachedScore 217 j = 0 ↔
      (256 * 217 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_218 : ∀ j : Fin 256,
    (cachedScore 218 j = 0 ↔
      (256 * 218 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_219 : ∀ j : Fin 256,
    (cachedScore 219 j = 0 ↔
      (256 * 219 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_220 : ∀ j : Fin 256,
    (cachedScore 220 j = 0 ↔
      (256 * 220 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_221 : ∀ j : Fin 256,
    (cachedScore 221 j = 0 ↔
      (256 * 221 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_222 : ∀ j : Fin 256,
    (cachedScore 222 j = 0 ↔
      (256 * 222 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_223 : ∀ j : Fin 256,
    (cachedScore 223 j = 0 ↔
      (256 * 223 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_224 : ∀ j : Fin 256,
    (cachedScore 224 j = 0 ↔
      (256 * 224 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_225 : ∀ j : Fin 256,
    (cachedScore 225 j = 0 ↔
      (256 * 225 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_226 : ∀ j : Fin 256,
    (cachedScore 226 j = 0 ↔
      (256 * 226 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_227 : ∀ j : Fin 256,
    (cachedScore 227 j = 0 ↔
      (256 * 227 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_228 : ∀ j : Fin 256,
    (cachedScore 228 j = 0 ↔
      (256 * 228 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_229 : ∀ j : Fin 256,
    (cachedScore 229 j = 0 ↔
      (256 * 229 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_230 : ∀ j : Fin 256,
    (cachedScore 230 j = 0 ↔
      (256 * 230 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_231 : ∀ j : Fin 256,
    (cachedScore 231 j = 0 ↔
      (256 * 231 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_232 : ∀ j : Fin 256,
    (cachedScore 232 j = 0 ↔
      (256 * 232 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_233 : ∀ j : Fin 256,
    (cachedScore 233 j = 0 ↔
      (256 * 233 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_234 : ∀ j : Fin 256,
    (cachedScore 234 j = 0 ↔
      (256 * 234 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_235 : ∀ j : Fin 256,
    (cachedScore 235 j = 0 ↔
      (256 * 235 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_236 : ∀ j : Fin 256,
    (cachedScore 236 j = 0 ↔
      (256 * 236 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_237 : ∀ j : Fin 256,
    (cachedScore 237 j = 0 ↔
      (256 * 237 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_238 : ∀ j : Fin 256,
    (cachedScore 238 j = 0 ↔
      (256 * 238 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_239 : ∀ j : Fin 256,
    (cachedScore 239 j = 0 ↔
      (256 * 239 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_240 : ∀ j : Fin 256,
    (cachedScore 240 j = 0 ↔
      (256 * 240 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_241 : ∀ j : Fin 256,
    (cachedScore 241 j = 0 ↔
      (256 * 241 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_242 : ∀ j : Fin 256,
    (cachedScore 242 j = 0 ↔
      (256 * 242 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_243 : ∀ j : Fin 256,
    (cachedScore 243 j = 0 ↔
      (256 * 243 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_244 : ∀ j : Fin 256,
    (cachedScore 244 j = 0 ↔
      (256 * 244 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_245 : ∀ j : Fin 256,
    (cachedScore 245 j = 0 ↔
      (256 * 245 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_246 : ∀ j : Fin 256,
    (cachedScore 246 j = 0 ↔
      (256 * 246 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_247 : ∀ j : Fin 256,
    (cachedScore 247 j = 0 ↔
      (256 * 247 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_248 : ∀ j : Fin 256,
    (cachedScore 248 j = 0 ↔
      (256 * 248 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_249 : ∀ j : Fin 256,
    (cachedScore 249 j = 0 ↔
      (256 * 249 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_250 : ∀ j : Fin 256,
    (cachedScore 250 j = 0 ↔
      (256 * 250 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_251 : ∀ j : Fin 256,
    (cachedScore 251 j = 0 ↔
      (256 * 251 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_252 : ∀ j : Fin 256,
    (cachedScore 252 j = 0 ↔
      (256 * 252 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_253 : ∀ j : Fin 256,
    (cachedScore 253 j = 0 ↔
      (256 * 253 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_254 : ∀ j : Fin 256,
    (cachedScore 254 j = 0 ↔
      (256 * 254 + j.val) ∈ zeroVertexList) := by
  decide +kernel

private theorem zero_block_255 : ∀ j : Fin 256,
    (cachedScore 255 j = 0 ↔
      (256 * 255 + j.val) ∈ zeroVertexList) := by
  decide +kernel

theorem zero_blocks_correct (k j : Fin 256) :
    (clearedScore (256 * k.val + j.val) = 0 ↔
      (256 * k.val + j.val) ∈ zeroVertexList) := by
  rw [← cachedScore_eq]
  fin_cases k
  · exact zero_block_0 j
  · exact zero_block_1 j
  · exact zero_block_2 j
  · exact zero_block_3 j
  · exact zero_block_4 j
  · exact zero_block_5 j
  · exact zero_block_6 j
  · exact zero_block_7 j
  · exact zero_block_8 j
  · exact zero_block_9 j
  · exact zero_block_10 j
  · exact zero_block_11 j
  · exact zero_block_12 j
  · exact zero_block_13 j
  · exact zero_block_14 j
  · exact zero_block_15 j
  · exact zero_block_16 j
  · exact zero_block_17 j
  · exact zero_block_18 j
  · exact zero_block_19 j
  · exact zero_block_20 j
  · exact zero_block_21 j
  · exact zero_block_22 j
  · exact zero_block_23 j
  · exact zero_block_24 j
  · exact zero_block_25 j
  · exact zero_block_26 j
  · exact zero_block_27 j
  · exact zero_block_28 j
  · exact zero_block_29 j
  · exact zero_block_30 j
  · exact zero_block_31 j
  · exact zero_block_32 j
  · exact zero_block_33 j
  · exact zero_block_34 j
  · exact zero_block_35 j
  · exact zero_block_36 j
  · exact zero_block_37 j
  · exact zero_block_38 j
  · exact zero_block_39 j
  · exact zero_block_40 j
  · exact zero_block_41 j
  · exact zero_block_42 j
  · exact zero_block_43 j
  · exact zero_block_44 j
  · exact zero_block_45 j
  · exact zero_block_46 j
  · exact zero_block_47 j
  · exact zero_block_48 j
  · exact zero_block_49 j
  · exact zero_block_50 j
  · exact zero_block_51 j
  · exact zero_block_52 j
  · exact zero_block_53 j
  · exact zero_block_54 j
  · exact zero_block_55 j
  · exact zero_block_56 j
  · exact zero_block_57 j
  · exact zero_block_58 j
  · exact zero_block_59 j
  · exact zero_block_60 j
  · exact zero_block_61 j
  · exact zero_block_62 j
  · exact zero_block_63 j
  · exact zero_block_64 j
  · exact zero_block_65 j
  · exact zero_block_66 j
  · exact zero_block_67 j
  · exact zero_block_68 j
  · exact zero_block_69 j
  · exact zero_block_70 j
  · exact zero_block_71 j
  · exact zero_block_72 j
  · exact zero_block_73 j
  · exact zero_block_74 j
  · exact zero_block_75 j
  · exact zero_block_76 j
  · exact zero_block_77 j
  · exact zero_block_78 j
  · exact zero_block_79 j
  · exact zero_block_80 j
  · exact zero_block_81 j
  · exact zero_block_82 j
  · exact zero_block_83 j
  · exact zero_block_84 j
  · exact zero_block_85 j
  · exact zero_block_86 j
  · exact zero_block_87 j
  · exact zero_block_88 j
  · exact zero_block_89 j
  · exact zero_block_90 j
  · exact zero_block_91 j
  · exact zero_block_92 j
  · exact zero_block_93 j
  · exact zero_block_94 j
  · exact zero_block_95 j
  · exact zero_block_96 j
  · exact zero_block_97 j
  · exact zero_block_98 j
  · exact zero_block_99 j
  · exact zero_block_100 j
  · exact zero_block_101 j
  · exact zero_block_102 j
  · exact zero_block_103 j
  · exact zero_block_104 j
  · exact zero_block_105 j
  · exact zero_block_106 j
  · exact zero_block_107 j
  · exact zero_block_108 j
  · exact zero_block_109 j
  · exact zero_block_110 j
  · exact zero_block_111 j
  · exact zero_block_112 j
  · exact zero_block_113 j
  · exact zero_block_114 j
  · exact zero_block_115 j
  · exact zero_block_116 j
  · exact zero_block_117 j
  · exact zero_block_118 j
  · exact zero_block_119 j
  · exact zero_block_120 j
  · exact zero_block_121 j
  · exact zero_block_122 j
  · exact zero_block_123 j
  · exact zero_block_124 j
  · exact zero_block_125 j
  · exact zero_block_126 j
  · exact zero_block_127 j
  · exact zero_block_128 j
  · exact zero_block_129 j
  · exact zero_block_130 j
  · exact zero_block_131 j
  · exact zero_block_132 j
  · exact zero_block_133 j
  · exact zero_block_134 j
  · exact zero_block_135 j
  · exact zero_block_136 j
  · exact zero_block_137 j
  · exact zero_block_138 j
  · exact zero_block_139 j
  · exact zero_block_140 j
  · exact zero_block_141 j
  · exact zero_block_142 j
  · exact zero_block_143 j
  · exact zero_block_144 j
  · exact zero_block_145 j
  · exact zero_block_146 j
  · exact zero_block_147 j
  · exact zero_block_148 j
  · exact zero_block_149 j
  · exact zero_block_150 j
  · exact zero_block_151 j
  · exact zero_block_152 j
  · exact zero_block_153 j
  · exact zero_block_154 j
  · exact zero_block_155 j
  · exact zero_block_156 j
  · exact zero_block_157 j
  · exact zero_block_158 j
  · exact zero_block_159 j
  · exact zero_block_160 j
  · exact zero_block_161 j
  · exact zero_block_162 j
  · exact zero_block_163 j
  · exact zero_block_164 j
  · exact zero_block_165 j
  · exact zero_block_166 j
  · exact zero_block_167 j
  · exact zero_block_168 j
  · exact zero_block_169 j
  · exact zero_block_170 j
  · exact zero_block_171 j
  · exact zero_block_172 j
  · exact zero_block_173 j
  · exact zero_block_174 j
  · exact zero_block_175 j
  · exact zero_block_176 j
  · exact zero_block_177 j
  · exact zero_block_178 j
  · exact zero_block_179 j
  · exact zero_block_180 j
  · exact zero_block_181 j
  · exact zero_block_182 j
  · exact zero_block_183 j
  · exact zero_block_184 j
  · exact zero_block_185 j
  · exact zero_block_186 j
  · exact zero_block_187 j
  · exact zero_block_188 j
  · exact zero_block_189 j
  · exact zero_block_190 j
  · exact zero_block_191 j
  · exact zero_block_192 j
  · exact zero_block_193 j
  · exact zero_block_194 j
  · exact zero_block_195 j
  · exact zero_block_196 j
  · exact zero_block_197 j
  · exact zero_block_198 j
  · exact zero_block_199 j
  · exact zero_block_200 j
  · exact zero_block_201 j
  · exact zero_block_202 j
  · exact zero_block_203 j
  · exact zero_block_204 j
  · exact zero_block_205 j
  · exact zero_block_206 j
  · exact zero_block_207 j
  · exact zero_block_208 j
  · exact zero_block_209 j
  · exact zero_block_210 j
  · exact zero_block_211 j
  · exact zero_block_212 j
  · exact zero_block_213 j
  · exact zero_block_214 j
  · exact zero_block_215 j
  · exact zero_block_216 j
  · exact zero_block_217 j
  · exact zero_block_218 j
  · exact zero_block_219 j
  · exact zero_block_220 j
  · exact zero_block_221 j
  · exact zero_block_222 j
  · exact zero_block_223 j
  · exact zero_block_224 j
  · exact zero_block_225 j
  · exact zero_block_226 j
  · exact zero_block_227 j
  · exact zero_block_228 j
  · exact zero_block_229 j
  · exact zero_block_230 j
  · exact zero_block_231 j
  · exact zero_block_232 j
  · exact zero_block_233 j
  · exact zero_block_234 j
  · exact zero_block_235 j
  · exact zero_block_236 j
  · exact zero_block_237 j
  · exact zero_block_238 j
  · exact zero_block_239 j
  · exact zero_block_240 j
  · exact zero_block_241 j
  · exact zero_block_242 j
  · exact zero_block_243 j
  · exact zero_block_244 j
  · exact zero_block_245 j
  · exact zero_block_246 j
  · exact zero_block_247 j
  · exact zero_block_248 j
  · exact zero_block_249 j
  · exact zero_block_250 j
  · exact zero_block_251 j
  · exact zero_block_252 j
  · exact zero_block_253 j
  · exact zero_block_254 j
  · exact zero_block_255 j

theorem all_base_zeros (v : Fin 65536) :
    clearedScore v.val = 0 ↔ v.val ∈ zeroVertexList := by
  let k : Fin 256 := ⟨v.val / 256, by omega⟩
  let j : Fin 256 := ⟨v.val % 256, Nat.mod_lt _ (by decide)⟩
  have h := zero_blocks_correct k j
  have he : 256 * k.val + j.val = v.val := by dsimp [k, j]; omega
  simpa only [he] using h

#print axioms all_base_zeros
#print axioms zeroVertexList_decomposition

end HeadComplexity.CoordinateZeroFiber
