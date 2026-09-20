import Coulomb8.BlockMatrix
import Coulomb8.FinitePositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.PSDBounds.S6_trivial

def preconditioner : Matrix (Fin 14) (Fin 14) ℤ := ![![2532313248007,0,0,0,0,0,0,0,0,0,0,0,0,0],![-1400799005718,2769819167273,0,0,0,0,0,0,0,0,0,0,0,0],![3714785505145,-4883264574556,6477912990547,0,0,0,0,0,0,0,0,0,0,0],![2045700028138,-690669044302,2387496226311,978597506157,0,0,0,0,0,0,0,0,0,0],![-8065844916992,5180560533885,-5524251981105,-1267135068753,2676752513769,0,0,0,0,0,0,0,0,0],![-22562131957585,10684654802175,-19374778253356,-2984111190452,-1372352992655,9402468335582,0,0,0,0,0,0,0,0],![27969111949971,-12257545957410,22573268764169,4998853351283,-2380201841010,-7816115223135,2408220642998,0,0,0,0,0,0,0],![-63547243232674,35744454561343,-50357319267987,-2664603458322,5050419312387,12375011524109,-6354927301968,9309715574312,0,0,0,0,0,0],![13822460552093,51076822095743,-16016460566589,26602947247881,-22534143930188,-23896513580526,27541542530872,4196479877960,79248109680876,0,0,0,0,0],![-9686093655117,17453026445435,11629373014759,5408552408503,42938845659511,-43143134252714,-14967197532207,15871280362162,-13001596428782,17873321212825,0,0,0,0],![8970542623601,1263189221055,5667227043646,25922690449591,-1445561681747,8671353210942,-5812429105171,24445996686178,-3265869149618,-6490764648734,83267903275382,0,0,0],![7803161314875,9271981412494,11392466921795,47648480997319,-12422204274027,6671234083164,-23249106695669,38049485569808,-31584427495784,-12739260002805,-36601538630368,33098826994523,0,0],![3452863569301,-2291730542006,4538103713439,12603107135277,14827181293822,21596624049530,2154555956838,4226512841283,25213522183201,22445131353235,-929662871692,8344365867908,102246909573848,0],![12536380305817,11401958544200,-19164740418808,3496919260334,2722788602114,-3206262814231,8924684444221,-11946345713805,-28763990873520,195039869712,7520535533348,14766905815005,-2411366387261,119382885217487]]
def boxes : Fin 14 → Fin 14 → Dyadic := ![![⟨64151120145778764701290755703300947968,64151120148254644779861516253099196416⟩,⟨32443571181827786419483508484308205568,32443571184303666498054269034106454016⟩,⟨-12330685755603966955625520492097568768,-12330685753128086877054759942299320320⟩,⟨-81122945626221219389716866942537564160,-81122945623745339311146106392739315712⟩,⟨66664944367376310049259761152414449664,66664944369852190127830521702212698112⟩,⟨75644107250499608200758377005637959680,75644107252975488279329137555436208128⟩,⟨15452644477227162937843150103957733376,15452644479703043016413910653755981824⟩,⟨97238860033836890705461239636222279680,97238860036312770784032000186020528128⟩,⟨23886903681104731081221109138459721728,23886903683580611159791869688257970176⟩,⟨2061433925887289209606661418921230336,2061433928363169288177421968719478784⟩,⟨-14400591644676030818085628456019689472,-14400591642200150739514867906221441024⟩,⟨13322328081821217103128103331827810304,13322328084297097181698863881626058752⟩,⟨-28443653655403000089176552166276464640,-28443653652927120010605791616478216192⟩,⟨4084718261123273047062394340559028224,4084718263599153125633154890357276672⟩],![⟨32443571181827786419483508484308205568,32443571184303666498054269034106454016⟩,⟨70029069770328087269259194056935735296,70029069772803967347829954606733983744⟩,⟨34185326038463656352295567912196898816,34185326040939536430866328461995147264⟩,⟨-101798993027321150425927052670885953536,-101798993024845270347356292121087705088⟩,⟨-15410367632412022666063384799998902272,-15410367629936142587492624250200653824⟩,⟨34157501970991778159233180538664648704,34157501973467658237803941088462897152⟩,⟨-33855063460494511434546316496571727872,-33855063458018631355975555946773479424⟩,⟨48203288569678238338999435221729804288,48203288572154118417570195771528052736⟩,⟨5419576006422362456778686135762157568,5419576008898242535349446685560406016⟩,⟨10022112960526634017289326884458332160,10022112963002514095860087434256580608⟩,⟨5461842681212171688498836289863286784,5461842683688051767069596839661535232⟩,⟨30722785090840315381120464597823782912,30722785093316195459691225147622031360⟩,⟨-748685111080656844618055287924850688,-748685108604776766047294738126602240⟩,⟨4127814333279313202709105409783758848,4127814335755193281279865959582007296⟩],![⟨-12330685755603966955625520492097568768,-12330685753128086877054759942299320320⟩,⟨34185326038463656352295567912196898816,34185326040939536430866328461995147264⟩,⟨42644331541908804579850545942071607296,42644331544384684658421306491869855744⟩,⟨-54136199654159056322186657794004877312,-54136199651683176243615897244206628864⟩,⟨-40936318704451686777294146170651672576,-40936318701975806698723385620853424128⟩,⟨-3719025385410974657560751597523304448,-3719025382935094578989991047725056000⟩,⟨-22672976859634917247551493449634021376,-22672976857159037168980732899835772928⟩,⟨11425615482320553753751621350920814592,11425615484796433832322381900719063040⟩,⟨1422381836301395499278525455335948288,1422381838777275577849286005134196736⟩,⟨9841991864385866196044120476165865472,9841991866861746274614881025964113920⟩,⟨10323497477216110780244935267336585216,10323497479691990858815695817134833664⟩,⟨29473032194444964838753084847150858240,29473032196920844917323845396949106688⟩,⟨7867460350533970437261223713382072320,7867460353009850515831984263180320768⟩,⟨6323030726872820251775919969571700736,6323030729348700330346680519369949184⟩],![⟨-81122945626221219389716866942537564160,-81122945623745339311146106392739315712⟩,⟨-101798993027321150425927052670885953536,-101798993024845270347356292121087705088⟩,⟨-54136199654159056322186657794004877312,-54136199651683176243615897244206628864⟩,⟨659379306436712375774801479360531398656,659379306439188255853372239910329647104⟩,⟨152988137508203213454959332423404355584,152988137510679093533530092973202604032⟩,⟨41065655699362556596162990387784318976,41065655701838436674733750937582567424⟩,⟨-152752621113396975314518109859598041088,-152752621110921095235947349309799792640⟩,⟨-508837628572305915980138782721203765248,-508837628569830035901568022171405516800⟩,⟨-16611917380575932714357076203940085760,-16611917378100052635786315654141837312⟩,⟨-65436622490168709412232539205193957376,-65436622487692829333661778655395708928⟩,⟨-59957354106598936801488741807536734208,-59957354104123056722917981257738485760⟩,⟨-463504879988248765804592475031482662912,-463504879985772885726021714481684414464⟩,⟨-29279990878701052487994388464768385024,-29279990876225172409423627914970136576⟩,⟨4973933031754907908058464653880066048,4973933034230787986629225203678314496⟩],![⟨66664944367376310049259761152414449664,66664944369852190127830521702212698112⟩,⟨-15410367632412022666063384799998902272,-15410367629936142587492624250200653824⟩,⟨-40936318704451686777294146170651672576,-40936318701975806698723385620853424128⟩,⟨152988137508203213454959332423404355584,152988137510679093533530092973202604032⟩,⟨276059263027700948321523088891286913024,276059263030176828400093849441085161472⟩,⟨181974556122612145125787743841784168448,181974556125088025204358504391582416896⟩,⟨76927977397560143128163020301509066752,76927977400036023206733780851307315200⟩,⟨-2563181260367542375112391841407827968,-2563181257891662296541631291609579520⟩,⟨45444699765543988588816077625445318656,45444699768019868667386838175243567104⟩,⟨-92679066524224390935313828704331759616,-92679066521748510856743068154533511168⟩,⟨-65267307197692659291669686806286172160,-65267307195216779213098926256487923712⟩,⟨-158117294220957641318107207769163563008,-158117294218481761239536447219365314560⟩,⟨-78172517109804694621106489108836909056,-78172517107328814542535728559038660608⟩,⟨9193709888011765308046326455378903040,9193709890487645386617087005177151488⟩],![⟨75644107250499608200758377005637959680,75644107252975488279329137555436208128⟩,⟨34157501970991778159233180538664648704,34157501973467658237803941088462897152⟩,⟨-3719025385410974657560751597523304448,-3719025382935094578989991047725056000⟩,⟨41065655699362556596162990387784318976,41065655701838436674733750937582567424⟩,⟨181974556122612145125787743841784168448,181974556125088025204358504391582416896⟩,⟨179283311524849441864622634296366071808,179283311527325321943193394846164320256⟩,⟨6682614016908770375459919516852551680,6682614019384650454030680066650800128⟩,⟨44358327509439242686256074677020524544,44358327511915122764826835226818772992⟩,⟨51388117414859402551475411551168495616,51388117417335282630046172100966744064⟩,⟨-3195879500787453877613773254016630784,-3195879498311573799043012704218382336⟩,⟨-47499735863520436047101459472276520960,-47499735861044555968530698922478272512⟩,⟨-104097132840395946410978547694586298368,-104097132837920066332407787144788049920⟩,⟨-76824105104667439626126947211355881472,-76824105102191559547556186661557633024⟩,⟨18301646075222268478590763076308434944,18301646077698148557161523626106683392⟩],![⟨15452644477227162937843150103957733376,15452644479703043016413910653755981824⟩,⟨-33855063460494511434546316496571727872,-33855063458018631355975555946773479424⟩,⟨-22672976859634917247551493449634021376,-22672976857159037168980732899835772928⟩,⟨-152752621113396975314518109859598041088,-152752621110921095235947349309799792640⟩,⟨76927977397560143128163020301509066752,76927977400036023206733780851307315200⟩,⟨6682614016908770375459919516852551680,6682614019384650454030680066650800128⟩,⟨346468345673536984534395424972520554496,346468345676012864612966185522318802944⟩,⟨254990971516473995089891539044945362944,254990971518949875168462299594743611392⟩,⟨-44202887808674190207266067200453115904,-44202887806198310128695306650654867456⟩,⟨-34720946622785383261843176655410954240,-34720946620309503183272416105612705792⟩,⟨-6530207586766606524834284649022750720,-6530207584290726446263524099224502272⟩,⟨148538068735591230148689117557368553472,148538068738067110227259878107166801920⟩,⟨-5513592490303552427013304220152496128,-5513592487827672348442543670354247680⟩,⟨-28180914547568779612137931839423643648,-28180914545092899533567171289625395200⟩],![⟨97238860033836890705461239636222279680,97238860036312770784032000186020528128⟩,⟨48203288569678238338999435221729804288,48203288572154118417570195771528052736⟩,⟨11425615482320553753751621350920814592,11425615484796433832322381900719063040⟩,⟨-508837628572305915980138782721203765248,-508837628569830035901568022171405516800⟩,⟨-2563181260367542375112391841407827968,-2563181257891662296541631291609579520⟩,⟨44358327509439242686256074677020524544,44358327511915122764826835226818772992⟩,⟨254990971516473995089891539044945362944,254990971518949875168462299594743611392⟩,⟨516065319030799584652219555152096395264,516065319033275464730790315701894643712⟩,⟨21794529634352227408577782337912176640,21794529636828107487148542887710425088⟩,⟨36525810881329261084696807206041944064,36525810883805141163267567755840192512⟩,⟨11754901383786594851315269533173809152,11754901386262474929886030082972057600⟩,⟨315960378001148356674049179399411990528,315960378003624236752619939949210238976⟩,⟨-14764630223950074487066303936268861440,-14764630221474194408495543386470612992⟩,⟨823338073556334169320655539752927232,823338076032214247891416089551175680⟩],![⟨23886903681104731081221109138459721728,23886903683580611159791869688257970176⟩,⟨5419576006422362456778686135762157568,5419576008898242535349446685560406016⟩,⟨1422381836301395499278525455335948288,1422381838777275577849286005134196736⟩,⟨-16611917380575932714357076203940085760,-16611917378100052635786315654141837312⟩,⟨45444699765543988588816077625445318656,45444699768019868667386838175243567104⟩,⟨51388117414859402551475411551168495616,51388117417335282630046172100966744064⟩,⟨-44202887808674190207266067200453115904,-44202887806198310128695306650654867456⟩,⟨21794529634352227408577782337912176640,21794529636828107487148542887710425088⟩,⟨40895835173550827274912577678317977600,40895835176026707353483338228116226048⟩,⟨-1237940039285380274899124224,1237940039285380274899124224⟩,⟨-10023380900451003908204552152879726592,-10023380897975123829633791603081478144⟩,⟨-5189371634618802402949224823919738880,-5189371632142922324378464274121490432⟩,⟨-25866791284275451450217302618280034304,-25866791281799571371646542068481785856⟩,⟨14122255487614210522259377944707203072,14122255490090090600830138494505451520⟩],![⟨2061433925887289209606661418921230336,2061433928363169288177421968719478784⟩,⟨10022112960526634017289326884458332160,10022112963002514095860087434256580608⟩,⟨9841991864385866196044120476165865472,9841991866861746274614881025964113920⟩,⟨-65436622490168709412232539205193957376,-65436622487692829333661778655395708928⟩,⟨-92679066524224390935313828704331759616,-92679066521748510856743068154533511168⟩,⟨-3195879500787453877613773254016630784,-3195879498311573799043012704218382336⟩,⟨-34720946622785383261843176655410954240,-34720946620309503183272416105612705792⟩,⟨36525810881329261084696807206041944064,36525810883805141163267567755840192512⟩,⟨-1237940039285380274899124224,1237940039285380274899124224⟩,⟨159443991854826024247959209401967968256,159443991857301904326529969951766216704⟩,⟨17333141216752296228637882755634429952,17333141219228176307208643305432678400⟩,⟨67538995067171370608967006649724174336,67538995069647250687537767199522422784⟩,⟨-19234670240650015641308329070905262080,-19234670238174135562737568521107013632⟩,⟨506580529500942486962284395445092352,506580531976822565533044945243340800⟩],![⟨-14400591644676030818085628456019689472,-14400591642200150739514867906221441024⟩,⟨5461842681212171688498836289863286784,5461842683688051767069596839661535232⟩,⟨10323497477216110780244935267336585216,10323497479691990858815695817134833664⟩,⟨-59957354106598936801488741807536734208,-59957354104123056722917981257738485760⟩,⟨-65267307197692659291669686806286172160,-65267307195216779213098926256487923712⟩,⟨-47499735863520436047101459472276520960,-47499735861044555968530698922478272512⟩,⟨-6530207586766606524834284649022750720,-6530207584290726446263524099224502272⟩,⟨11754901383786594851315269533173809152,11754901386262474929886030082972057600⟩,⟨-10023380900451003908204552152879726592,-10023380897975123829633791603081478144⟩,⟨17333141216752296228637882755634429952,17333141219228176307208643305432678400⟩,⟨20355564898418093879952918023143161856,20355564900893973958523678572941410304⟩,⟨71219956272686667062850447485693853696,71219956275162547141421208035492102144⟩,⟨19729792807292054450980027440690102272,19729792809767934529550787990488350720⟩,⟨-5855203608024206075141588097920139264,-5855203605548325996570827548121890816⟩],![⟨13322328081821217103128103331827810304,13322328084297097181698863881626058752⟩,⟨30722785090840315381120464597823782912,30722785093316195459691225147622031360⟩,⟨29473032194444964838753084847150858240,29473032196920844917323845396949106688⟩,⟨-463504879988248765804592475031482662912,-463504879985772885726021714481684414464⟩,⟨-158117294220957641318107207769163563008,-158117294218481761239536447219365314560⟩,⟨-104097132840395946410978547694586298368,-104097132837920066332407787144788049920⟩,⟨148538068735591230148689117557368553472,148538068738067110227259878107166801920⟩,⟨315960378001148356674049179399411990528,315960378003624236752619939949210238976⟩,⟨-5189371634618802402949224823919738880,-5189371632142922324378464274121490432⟩,⟨67538995067171370608967006649724174336,67538995069647250687537767199522422784⟩,⟨71219956272686667062850447485693853696,71219956275162547141421208035492102144⟩,⟨448291908476155115032568764704401391616,448291908478630995111139525254199640064⟩,⟨35304871178013407558438241549145866240,35304871180489287637009002098944114688⟩,⟨-25286382344479219210376600529752031232,-25286382342003339131805839979953782784⟩],![⟨-28443653655403000089176552166276464640,-28443653652927120010605791616478216192⟩,⟨-748685111080656844618055287924850688,-748685108604776766047294738126602240⟩,⟨7867460350533970437261223713382072320,7867460353009850515831984263180320768⟩,⟨-29279990878701052487994388464768385024,-29279990876225172409423627914970136576⟩,⟨-78172517109804694621106489108836909056,-78172517107328814542535728559038660608⟩,⟨-76824105104667439626126947211355881472,-76824105102191559547556186661557633024⟩,⟨-5513592490303552427013304220152496128,-5513592487827672348442543670354247680⟩,⟨-14764630223950074487066303936268861440,-14764630221474194408495543386470612992⟩,⟨-25866791284275451450217302618280034304,-25866791281799571371646542068481785856⟩,⟨-19234670240650015641308329070905262080,-19234670238174135562737568521107013632⟩,⟨19729792807292054450980027440690102272,19729792809767934529550787990488350720⟩,⟨35304871178013407558438241549145866240,35304871180489287637009002098944114688⟩,⟨40431536862804915417127459480127143936,40431536865280795495698220029925392384⟩,⟨-7160745755221811794290959274253221888,-7160745752745931715720198724454973440⟩],![⟨4084718261123273047062394340559028224,4084718263599153125633154890357276672⟩,⟨4127814333279313202709105409783758848,4127814335755193281279865959582007296⟩,⟨6323030726872820251775919969571700736,6323030729348700330346680519369949184⟩,⟨4973933031754907908058464653880066048,4973933034230787986629225203678314496⟩,⟨9193709888011765308046326455378903040,9193709890487645386617087005177151488⟩,⟨18301646075222268478590763076308434944,18301646077698148557161523626106683392⟩,⟨-28180914547568779612137931839423643648,-28180914545092899533567171289625395200⟩,⟨823338073556334169320655539752927232,823338076032214247891416089551175680⟩,⟨14122255487614210522259377944707203072,14122255490090090600830138494505451520⟩,⟨506580529500942486962284395445092352,506580531976822565533044945243340800⟩,⟨-5855203608024206075141588097920139264,-5855203605548325996570827548121890816⟩,⟨-25286382344479219210376600529752031232,-25286382342003339131805839979953782784⟩,⟨-7160745755221811794290959274253221888,-7160745752745931715720198724454973440⟩,⟨9299743843803634382311132491023384576,9299743846279514460881893040821633024⟩]]

theorem contains (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ))
    (i j : Fin 14) : (boxes i j).Contains (Data.S6_trivial.matrixFrom w i j) := by
  fin_cases i <;> fin_cases j
  · exact centerBox_contains w h 45
  · exact centerBox_contains w h 46
  · exact centerBox_contains w h 47
  · exact centerBox_contains w h 48
  · exact centerBox_contains w h 49
  · exact centerBox_contains w h 50
  · exact centerBox_contains w h 51
  · exact centerBox_contains w h 52
  · exact centerBox_contains w h 53
  · exact centerBox_contains w h 54
  · exact centerBox_contains w h 55
  · exact centerBox_contains w h 56
  · exact centerBox_contains w h 57
  · exact centerBox_contains w h 58
  · exact centerBox_contains w h 46
  · exact centerBox_contains w h 59
  · exact centerBox_contains w h 60
  · exact centerBox_contains w h 61
  · exact centerBox_contains w h 62
  · exact centerBox_contains w h 63
  · exact centerBox_contains w h 64
  · exact centerBox_contains w h 65
  · exact centerBox_contains w h 66
  · exact centerBox_contains w h 67
  · exact centerBox_contains w h 68
  · exact centerBox_contains w h 69
  · exact centerBox_contains w h 70
  · exact centerBox_contains w h 71
  · exact centerBox_contains w h 47
  · exact centerBox_contains w h 60
  · exact centerBox_contains w h 72
  · exact centerBox_contains w h 73
  · exact centerBox_contains w h 74
  · exact centerBox_contains w h 75
  · exact centerBox_contains w h 76
  · exact centerBox_contains w h 77
  · exact centerBox_contains w h 78
  · exact centerBox_contains w h 79
  · exact centerBox_contains w h 80
  · exact centerBox_contains w h 81
  · exact centerBox_contains w h 82
  · exact centerBox_contains w h 83
  · exact centerBox_contains w h 48
  · exact centerBox_contains w h 61
  · exact centerBox_contains w h 73
  · exact centerBox_contains w h 84
  · exact centerBox_contains w h 85
  · exact centerBox_contains w h 86
  · exact centerBox_contains w h 87
  · exact centerBox_contains w h 88
  · exact centerBox_contains w h 89
  · exact centerBox_contains w h 90
  · exact centerBox_contains w h 91
  · exact centerBox_contains w h 92
  · exact centerBox_contains w h 93
  · exact centerBox_contains w h 94
  · exact centerBox_contains w h 49
  · exact centerBox_contains w h 62
  · exact centerBox_contains w h 74
  · exact centerBox_contains w h 85
  · exact centerBox_contains w h 95
  · exact centerBox_contains w h 96
  · exact centerBox_contains w h 97
  · exact centerBox_contains w h 98
  · exact centerBox_contains w h 99
  · exact centerBox_contains w h 100
  · exact centerBox_contains w h 101
  · exact centerBox_contains w h 102
  · exact centerBox_contains w h 103
  · exact centerBox_contains w h 104
  · exact centerBox_contains w h 50
  · exact centerBox_contains w h 63
  · exact centerBox_contains w h 75
  · exact centerBox_contains w h 86
  · exact centerBox_contains w h 96
  · exact centerBox_contains w h 105
  · exact centerBox_contains w h 106
  · exact centerBox_contains w h 107
  · exact centerBox_contains w h 108
  · exact centerBox_contains w h 109
  · exact centerBox_contains w h 110
  · exact centerBox_contains w h 111
  · exact centerBox_contains w h 112
  · exact centerBox_contains w h 113
  · exact centerBox_contains w h 51
  · exact centerBox_contains w h 64
  · exact centerBox_contains w h 76
  · exact centerBox_contains w h 87
  · exact centerBox_contains w h 97
  · exact centerBox_contains w h 106
  · exact centerBox_contains w h 114
  · exact centerBox_contains w h 115
  · exact centerBox_contains w h 116
  · exact centerBox_contains w h 117
  · exact centerBox_contains w h 118
  · exact centerBox_contains w h 119
  · exact centerBox_contains w h 120
  · exact centerBox_contains w h 121
  · exact centerBox_contains w h 52
  · exact centerBox_contains w h 65
  · exact centerBox_contains w h 77
  · exact centerBox_contains w h 88
  · exact centerBox_contains w h 98
  · exact centerBox_contains w h 107
  · exact centerBox_contains w h 115
  · exact centerBox_contains w h 122
  · exact centerBox_contains w h 123
  · exact centerBox_contains w h 124
  · exact centerBox_contains w h 125
  · exact centerBox_contains w h 126
  · exact centerBox_contains w h 127
  · exact centerBox_contains w h 128
  · exact centerBox_contains w h 53
  · exact centerBox_contains w h 66
  · exact centerBox_contains w h 78
  · exact centerBox_contains w h 89
  · exact centerBox_contains w h 99
  · exact centerBox_contains w h 108
  · exact centerBox_contains w h 116
  · exact centerBox_contains w h 123
  · exact centerBox_contains w h 129
  · exact centerBox_contains w h 130
  · exact centerBox_contains w h 131
  · exact centerBox_contains w h 132
  · exact centerBox_contains w h 133
  · exact centerBox_contains w h 134
  · exact centerBox_contains w h 54
  · exact centerBox_contains w h 67
  · exact centerBox_contains w h 79
  · exact centerBox_contains w h 90
  · exact centerBox_contains w h 100
  · exact centerBox_contains w h 109
  · exact centerBox_contains w h 117
  · exact centerBox_contains w h 124
  · exact centerBox_contains w h 130
  · exact centerBox_contains w h 135
  · exact centerBox_contains w h 136
  · exact centerBox_contains w h 137
  · exact centerBox_contains w h 138
  · exact centerBox_contains w h 139
  · exact centerBox_contains w h 55
  · exact centerBox_contains w h 68
  · exact centerBox_contains w h 80
  · exact centerBox_contains w h 91
  · exact centerBox_contains w h 101
  · exact centerBox_contains w h 110
  · exact centerBox_contains w h 118
  · exact centerBox_contains w h 125
  · exact centerBox_contains w h 131
  · exact centerBox_contains w h 136
  · exact centerBox_contains w h 140
  · exact centerBox_contains w h 141
  · exact centerBox_contains w h 142
  · exact centerBox_contains w h 143
  · exact centerBox_contains w h 56
  · exact centerBox_contains w h 69
  · exact centerBox_contains w h 81
  · exact centerBox_contains w h 92
  · exact centerBox_contains w h 102
  · exact centerBox_contains w h 111
  · exact centerBox_contains w h 119
  · exact centerBox_contains w h 126
  · exact centerBox_contains w h 132
  · exact centerBox_contains w h 137
  · exact centerBox_contains w h 141
  · exact centerBox_contains w h 144
  · exact centerBox_contains w h 145
  · exact centerBox_contains w h 146
  · exact centerBox_contains w h 57
  · exact centerBox_contains w h 70
  · exact centerBox_contains w h 82
  · exact centerBox_contains w h 93
  · exact centerBox_contains w h 103
  · exact centerBox_contains w h 112
  · exact centerBox_contains w h 120
  · exact centerBox_contains w h 127
  · exact centerBox_contains w h 133
  · exact centerBox_contains w h 138
  · exact centerBox_contains w h 142
  · exact centerBox_contains w h 145
  · exact centerBox_contains w h 147
  · exact centerBox_contains w h 148
  · exact centerBox_contains w h 58
  · exact centerBox_contains w h 71
  · exact centerBox_contains w h 83
  · exact centerBox_contains w h 94
  · exact centerBox_contains w h 104
  · exact centerBox_contains w h 113
  · exact centerBox_contains w h 121
  · exact centerBox_contains w h 128
  · exact centerBox_contains w h 134
  · exact centerBox_contains w h 139
  · exact centerBox_contains w h 143
  · exact centerBox_contains w h 146
  · exact centerBox_contains w h 148
  · exact centerBox_contains w h 149

theorem checked0_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked8_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 8 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (8 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked9_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 9 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (9 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked10_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 10 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (10 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked11_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 11 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (11 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked12_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 12 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (12 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_8 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 8 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 8) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_9 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 9 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 9) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_10 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 10 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 10) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_11 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 11 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 11) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_12 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 12 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 12) (2^80) ≤ 2^203 := by decide +kernel

theorem checked13_13 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 13 k*preconditioner 13 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (13 : Fin 14) 13) (2^80) ≤ 2^203 := by decide +kernel

theorem positive (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) :
    (Data.S6_trivial.matrixFrom w).PosDef := by
  apply posDef_of_entry_bounds (Dyadic.scaledMatrix preconditioner) _ (by decide)
    (Data.S6_trivial.matrixFrom_symm w)
  intro i j
  apply Dyadic.congruence_entry_bound _ _ boxes (contains w h)
  fin_cases i <;> fin_cases j
  · exact checked0_0
  · exact checked0_1
  · exact checked0_2
  · exact checked0_3
  · exact checked0_4
  · exact checked0_5
  · exact checked0_6
  · exact checked0_7
  · exact checked0_8
  · exact checked0_9
  · exact checked0_10
  · exact checked0_11
  · exact checked0_12
  · exact checked0_13
  · exact checked1_0
  · exact checked1_1
  · exact checked1_2
  · exact checked1_3
  · exact checked1_4
  · exact checked1_5
  · exact checked1_6
  · exact checked1_7
  · exact checked1_8
  · exact checked1_9
  · exact checked1_10
  · exact checked1_11
  · exact checked1_12
  · exact checked1_13
  · exact checked2_0
  · exact checked2_1
  · exact checked2_2
  · exact checked2_3
  · exact checked2_4
  · exact checked2_5
  · exact checked2_6
  · exact checked2_7
  · exact checked2_8
  · exact checked2_9
  · exact checked2_10
  · exact checked2_11
  · exact checked2_12
  · exact checked2_13
  · exact checked3_0
  · exact checked3_1
  · exact checked3_2
  · exact checked3_3
  · exact checked3_4
  · exact checked3_5
  · exact checked3_6
  · exact checked3_7
  · exact checked3_8
  · exact checked3_9
  · exact checked3_10
  · exact checked3_11
  · exact checked3_12
  · exact checked3_13
  · exact checked4_0
  · exact checked4_1
  · exact checked4_2
  · exact checked4_3
  · exact checked4_4
  · exact checked4_5
  · exact checked4_6
  · exact checked4_7
  · exact checked4_8
  · exact checked4_9
  · exact checked4_10
  · exact checked4_11
  · exact checked4_12
  · exact checked4_13
  · exact checked5_0
  · exact checked5_1
  · exact checked5_2
  · exact checked5_3
  · exact checked5_4
  · exact checked5_5
  · exact checked5_6
  · exact checked5_7
  · exact checked5_8
  · exact checked5_9
  · exact checked5_10
  · exact checked5_11
  · exact checked5_12
  · exact checked5_13
  · exact checked6_0
  · exact checked6_1
  · exact checked6_2
  · exact checked6_3
  · exact checked6_4
  · exact checked6_5
  · exact checked6_6
  · exact checked6_7
  · exact checked6_8
  · exact checked6_9
  · exact checked6_10
  · exact checked6_11
  · exact checked6_12
  · exact checked6_13
  · exact checked7_0
  · exact checked7_1
  · exact checked7_2
  · exact checked7_3
  · exact checked7_4
  · exact checked7_5
  · exact checked7_6
  · exact checked7_7
  · exact checked7_8
  · exact checked7_9
  · exact checked7_10
  · exact checked7_11
  · exact checked7_12
  · exact checked7_13
  · exact checked8_0
  · exact checked8_1
  · exact checked8_2
  · exact checked8_3
  · exact checked8_4
  · exact checked8_5
  · exact checked8_6
  · exact checked8_7
  · exact checked8_8
  · exact checked8_9
  · exact checked8_10
  · exact checked8_11
  · exact checked8_12
  · exact checked8_13
  · exact checked9_0
  · exact checked9_1
  · exact checked9_2
  · exact checked9_3
  · exact checked9_4
  · exact checked9_5
  · exact checked9_6
  · exact checked9_7
  · exact checked9_8
  · exact checked9_9
  · exact checked9_10
  · exact checked9_11
  · exact checked9_12
  · exact checked9_13
  · exact checked10_0
  · exact checked10_1
  · exact checked10_2
  · exact checked10_3
  · exact checked10_4
  · exact checked10_5
  · exact checked10_6
  · exact checked10_7
  · exact checked10_8
  · exact checked10_9
  · exact checked10_10
  · exact checked10_11
  · exact checked10_12
  · exact checked10_13
  · exact checked11_0
  · exact checked11_1
  · exact checked11_2
  · exact checked11_3
  · exact checked11_4
  · exact checked11_5
  · exact checked11_6
  · exact checked11_7
  · exact checked11_8
  · exact checked11_9
  · exact checked11_10
  · exact checked11_11
  · exact checked11_12
  · exact checked11_13
  · exact checked12_0
  · exact checked12_1
  · exact checked12_2
  · exact checked12_3
  · exact checked12_4
  · exact checked12_5
  · exact checked12_6
  · exact checked12_7
  · exact checked12_8
  · exact checked12_9
  · exact checked12_10
  · exact checked12_11
  · exact checked12_12
  · exact checked12_13
  · exact checked13_0
  · exact checked13_1
  · exact checked13_2
  · exact checked13_3
  · exact checked13_4
  · exact checked13_5
  · exact checked13_6
  · exact checked13_7
  · exact checked13_8
  · exact checked13_9
  · exact checked13_10
  · exact checked13_11
  · exact checked13_12
  · exact checked13_13

end Coulomb8.PSDBounds.S6_trivial

#print axioms Coulomb8.PSDBounds.S6_trivial.positive
