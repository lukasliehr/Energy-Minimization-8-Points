import ThomsonNegative.Certificate.Correction.q09.BlockData
import ThomsonNegative.Certificate.Correction.RowKernel
import ThomsonNegative.Certificate.Correction.SourceData

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

noncomputable def witness0 : RowWitness := ⟨Source.r0n, Source.r0d, norm0, inverse0, centers0, models0, (fun j => columns0.getD j 0), 3094, 47, 1024⟩
noncomputable def witness1 : RowWitness := ⟨Source.r1n, Source.r1d, norm1, inverse1, centers1, models1, (fun j => columns1.getD j 0), 3094, 46, 1024⟩
noncomputable def witness2 : RowWitness := ⟨Source.r2n, Source.r2d, norm2, inverse2, centers2, models2, (fun j => columns2.getD j 0), 3094, 45, 1024⟩
noncomputable def witness3 : RowWitness := ⟨Source.r3n, Source.r3d, norm3, inverse3, centers3, models3, (fun j => columns3.getD j 0), 3094, 44, 1024⟩
noncomputable def witness4 : RowWitness := ⟨Source.r4n, Source.r4d, norm4, inverse4, centers4, models4, (fun j => columns4.getD j 0), 3094, 43, 1024⟩
noncomputable def witness5 : RowWitness := ⟨Source.r5n, Source.r5d, norm5, inverse5, centers5, models5, (fun j => columns5.getD j 0), 3094, 42, 1024⟩
noncomputable def witness6 : RowWitness := ⟨Source.r6n, Source.r6d, norm6, inverse6, centers6, models6, (fun j => columns6.getD j 0), 3094, 45, 1024⟩
noncomputable def witness7 : RowWitness := ⟨Source.r7n, Source.r7d, norm7, inverse7, centers7, models7, (fun j => columns7.getD j 0), 3094, 44, 1024⟩
noncomputable def witness8 : RowWitness := ⟨Source.r8n, Source.r8d, norm8, inverse8, centers8, models8, (fun j => columns8.getD j 0), 3094, 43, 1024⟩
noncomputable def witness9 : RowWitness := ⟨Source.r9n, Source.r9d, norm9, inverse9, centers9, models9, (fun j => columns9.getD j 0), 3094, 42, 1024⟩
noncomputable def witness10 : RowWitness := ⟨Source.r10n, Source.r10d, norm10, inverse10, centers10, models10, (fun j => columns10.getD j 0), 3094, 41, 1024⟩
noncomputable def witness11 : RowWitness := ⟨Source.r11n, Source.r11d, norm11, inverse11, centers11, models11, (fun j => columns11.getD j 0), 3078, 1, 1024⟩
noncomputable def witness12 : RowWitness := ⟨Source.r12n, Source.r12d, norm12, inverse12, centers12, models12, (fun j => columns12.getD j 0), 3078, 1, 1024⟩
noncomputable def witness13 : RowWitness := ⟨Source.r13n, Source.r13d, norm13, inverse13, centers13, models13, (fun j => columns13.getD j 0), 3092, 28, 1024⟩
noncomputable def witness14 : RowWitness := ⟨Source.r14n, Source.r14d, norm14, inverse14, centers14, models14, (fun j => columns14.getD j 0), 3091, 24, 1024⟩
noncomputable def witness15 : RowWitness := ⟨Source.r15n, Source.r15d, norm15, inverse15, centers15, models15, (fun j => columns15.getD j 0), 3092, 25, 1024⟩
noncomputable def witness16 : RowWitness := ⟨Source.r16n, Source.r16d, norm16, inverse16, centers16, models16, (fun j => columns16.getD j 0), 3091, 23, 1024⟩
noncomputable def witness17 : RowWitness := ⟨Source.r17n, Source.r17d, norm17, inverse17, centers17, models17, (fun j => columns17.getD j 0), 3078, 1, 1024⟩
noncomputable def witness18 : RowWitness := ⟨Source.r18n, Source.r18d, norm18, inverse18, centers18, models18, (fun j => columns18.getD j 0), 3125, 62, 1034⟩
noncomputable def witness19 : RowWitness := ⟨Source.r19n, Source.r19d, norm19, inverse19, centers19, models19, (fun j => columns19.getD j 0), 3095, 58, 1024⟩
noncomputable def witness20 : RowWitness := ⟨Source.r20n, Source.r20d, norm20, inverse20, centers20, models20, (fun j => columns20.getD j 0), 3131, 62, 1036⟩
noncomputable def witness21 : RowWitness := ⟨Source.r21n, Source.r21d, norm21, inverse21, centers21, models21, (fun j => columns21.getD j 0), 3095, 60, 1024⟩
noncomputable def witness22 : RowWitness := ⟨Source.r22n, Source.r22d, norm22, inverse22, centers22, models22, (fun j => columns22.getD j 0), 3219, 64, 1065⟩
noncomputable def witness23 : RowWitness := ⟨Source.r23n, Source.r23d, norm23, inverse23, centers23, models23, (fun j => columns23.getD j 0), 3258, 65, 1078⟩
noncomputable def witness24 : RowWitness := ⟨Source.r24n, Source.r24d, norm24, inverse24, centers24, models24, (fun j => columns24.getD j 0), 3095, 55, 1024⟩
noncomputable def witness25 : RowWitness := ⟨Source.r25n, Source.r25d, norm25, inverse25, centers25, models25, (fun j => columns25.getD j 0), 3095, 60, 1024⟩
noncomputable def witness26 : RowWitness := ⟨Source.r26n, Source.r26d, norm26, inverse26, centers26, models26, (fun j => columns26.getD j 0), 3095, 59, 1024⟩
noncomputable def witness27 : RowWitness := ⟨Source.r27n, Source.r27d, norm27, inverse27, centers27, models27, (fun j => columns27.getD j 0), 3095, 60, 1024⟩
noncomputable def witness28 : RowWitness := ⟨Source.r28n, Source.r28d, norm28, inverse28, centers28, models28, (fun j => columns28.getD j 0), 3089, 13, 1024⟩
noncomputable def witness29 : RowWitness := ⟨Source.r29n, Source.r29d, norm29, inverse29, centers29, models29, (fun j => columns29.getD j 0), 3095, 55, 1024⟩
noncomputable def witness30 : RowWitness := ⟨Source.r30n, Source.r30d, norm30, inverse30, centers30, models30, (fun j => columns30.getD j 0), 3264, 65, 1080⟩
noncomputable def witness31 : RowWitness := ⟨Source.r31n, Source.r31d, norm31, inverse31, centers31, models31, (fun j => columns31.getD j 0), 3095, 56, 1024⟩
noncomputable def witness32 : RowWitness := ⟨Source.r32n, Source.r32d, norm32, inverse32, centers32, models32, (fun j => columns32.getD j 0), 3095, 54, 1024⟩
noncomputable def witness33 : RowWitness := ⟨Source.r33n, Source.r33d, norm33, inverse33, centers33, models33, (fun j => columns33.getD j 0), 3095, 60, 1024⟩
noncomputable def witness34 : RowWitness := ⟨Source.r34n, Source.r34d, norm34, inverse34, centers34, models34, (fun j => columns34.getD j 0), 3095, 51, 1024⟩
noncomputable def witness35 : RowWitness := ⟨Source.r35n, Source.r35d, norm35, inverse35, centers35, models35, (fun j => columns35.getD j 0), 3095, 55, 1024⟩
noncomputable def witness36 : RowWitness := ⟨Source.r36n, Source.r36d, norm36, inverse36, centers36, models36, (fun j => columns36.getD j 0), 3095, 54, 1024⟩
noncomputable def witness37 : RowWitness := ⟨Source.r37n, Source.r37d, norm37, inverse37, centers37, models37, (fun j => columns37.getD j 0), 3095, 55, 1024⟩
noncomputable def witness38 : RowWitness := ⟨Source.r38n, Source.r38d, norm38, inverse38, centers38, models38, (fun j => columns38.getD j 0), 3249, 65, 1075⟩
noncomputable def witness39 : RowWitness := ⟨Source.r39n, Source.r39d, norm39, inverse39, centers39, models39, (fun j => columns39.getD j 0), 3095, 60, 1024⟩
noncomputable def witness40 : RowWitness := ⟨Source.r40n, Source.r40d, norm40, inverse40, centers40, models40, (fun j => columns40.getD j 0), 3095, 58, 1024⟩
noncomputable def witness41 : RowWitness := ⟨Source.r41n, Source.r41d, norm41, inverse41, centers41, models41, (fun j => columns41.getD j 0), 3095, 54, 1024⟩
noncomputable def witness42 : RowWitness := ⟨Source.r42n, Source.r42d, norm42, inverse42, centers42, models42, (fun j => columns42.getD j 0), 3095, 51, 1024⟩
noncomputable def witness43 : RowWitness := ⟨Source.r43n, Source.r43d, norm43, inverse43, centers43, models43, (fun j => columns43.getD j 0), 3094, 41, 1024⟩
noncomputable def witness44 : RowWitness := ⟨Source.r44n, Source.r44d, norm44, inverse44, centers44, models44, (fun j => columns44.getD j 0), 3085, 6, 1024⟩
noncomputable def witness45 : RowWitness := ⟨Source.r45n, Source.r45d, norm45, inverse45, centers45, models45, (fun j => columns45.getD j 0), 3078, 1, 1024⟩
noncomputable def witness46 : RowWitness := ⟨Source.r46n, Source.r46d, norm46, inverse46, centers46, models46, (fun j => columns46.getD j 0), 3094, 49, 1024⟩
noncomputable def witness47 : RowWitness := ⟨Source.r47n, Source.r47d, norm47, inverse47, centers47, models47, (fun j => columns47.getD j 0), 3088, 12, 1024⟩
noncomputable def witness48 : RowWitness := ⟨Source.r48n, Source.r48d, norm48, inverse48, centers48, models48, (fun j => columns48.getD j 0), 3085, 6, 1024⟩
noncomputable def witness49 : RowWitness := ⟨Source.r49n, Source.r49d, norm49, inverse49, centers49, models49, (fun j => columns49.getD j 0), 3095, 51, 1024⟩
noncomputable def witness50 : RowWitness := ⟨Source.r50n, Source.r50d, norm50, inverse50, centers50, models50, (fun j => columns50.getD j 0), 3085, 6, 1024⟩
noncomputable def witness51 : RowWitness := ⟨Source.r51n, Source.r51d, norm51, inverse51, centers51, models51, (fun j => columns51.getD j 0), 3085, 6, 1024⟩
noncomputable def witness52 : RowWitness := ⟨Source.r52n, Source.r52d, norm52, inverse52, centers52, models52, (fun j => columns52.getD j 0), 3085, 6, 1024⟩
noncomputable def witness53 : RowWitness := ⟨Source.r53n, Source.r53d, norm53, inverse53, centers53, models53, (fun j => columns53.getD j 0), 3085, 6, 1024⟩
noncomputable def witness54 : RowWitness := ⟨Source.r54n, Source.r54d, norm54, inverse54, centers54, models54, (fun j => columns54.getD j 0), 3085, 6, 1024⟩
noncomputable def witness55 : RowWitness := ⟨Source.r55n, Source.r55d, norm55, inverse55, centers55, models55, (fun j => columns55.getD j 0), 3085, 6, 1024⟩
noncomputable def witness56 : RowWitness := ⟨Source.r56n, Source.r56d, norm56, inverse56, centers56, models56, (fun j => columns56.getD j 0), 3085, 6, 1024⟩
noncomputable def witness57 : RowWitness := ⟨Source.r57n, Source.r57d, norm57, inverse57, centers57, models57, (fun j => columns57.getD j 0), 3085, 6, 1024⟩
noncomputable def witness58 : RowWitness := ⟨Source.r58n, Source.r58d, norm58, inverse58, centers58, models58, (fun j => columns58.getD j 0), 3085, 6, 1024⟩
noncomputable def witness59 : RowWitness := ⟨Source.r59n, Source.r59d, norm59, inverse59, centers59, models59, (fun j => columns59.getD j 0), 3085, 6, 1024⟩
noncomputable def witness60 : RowWitness := ⟨Source.r60n, Source.r60d, norm60, inverse60, centers60, models60, (fun j => columns60.getD j 0), 3085, 6, 1024⟩
noncomputable def witness61 : RowWitness := ⟨Source.r61n, Source.r61d, norm61, inverse61, centers61, models61, (fun j => columns61.getD j 0), 3085, 6, 1024⟩
noncomputable def witness62 : RowWitness := ⟨Source.r62n, Source.r62d, norm62, inverse62, centers62, models62, (fun j => columns62.getD j 0), 3094, 49, 1024⟩
noncomputable def witness63 : RowWitness := ⟨Source.r63n, Source.r63d, norm63, inverse63, centers63, models63, (fun j => columns63.getD j 0), 3095, 51, 1024⟩
noncomputable def witness64 : RowWitness := ⟨Source.r64n, Source.r64d, norm64, inverse64, centers64, models64, (fun j => columns64.getD j 0), 3094, 49, 1024⟩
noncomputable def witness65 : RowWitness := ⟨Source.r65n, Source.r65d, norm65, inverse65, centers65, models65, (fun j => columns65.getD j 0), 3085, 6, 1024⟩
noncomputable def witness66 : RowWitness := ⟨Source.r66n, Source.r66d, norm66, inverse66, centers66, models66, (fun j => columns66.getD j 0), 3085, 6, 1024⟩
noncomputable def witness67 : RowWitness := ⟨Source.r67n, Source.r67d, norm67, inverse67, centers67, models67, (fun j => columns67.getD j 0), 3085, 6, 1024⟩
noncomputable def witness (r : Fin 68) : RowWitness := match r.val with
  | 0 => witness0
  | 1 => witness1
  | 2 => witness2
  | 3 => witness3
  | 4 => witness4
  | 5 => witness5
  | 6 => witness6
  | 7 => witness7
  | 8 => witness8
  | 9 => witness9
  | 10 => witness10
  | 11 => witness11
  | 12 => witness12
  | 13 => witness13
  | 14 => witness14
  | 15 => witness15
  | 16 => witness16
  | 17 => witness17
  | 18 => witness18
  | 19 => witness19
  | 20 => witness20
  | 21 => witness21
  | 22 => witness22
  | 23 => witness23
  | 24 => witness24
  | 25 => witness25
  | 26 => witness26
  | 27 => witness27
  | 28 => witness28
  | 29 => witness29
  | 30 => witness30
  | 31 => witness31
  | 32 => witness32
  | 33 => witness33
  | 34 => witness34
  | 35 => witness35
  | 36 => witness36
  | 37 => witness37
  | 38 => witness38
  | 39 => witness39
  | 40 => witness40
  | 41 => witness41
  | 42 => witness42
  | 43 => witness43
  | 44 => witness44
  | 45 => witness45
  | 46 => witness46
  | 47 => witness47
  | 48 => witness48
  | 49 => witness49
  | 50 => witness50
  | 51 => witness51
  | 52 => witness52
  | 53 => witness53
  | 54 => witness54
  | 55 => witness55
  | 56 => witness56
  | 57 => witness57
  | 58 => witness58
  | 59 => witness59
  | 60 => witness60
  | 61 => witness61
  | 62 => witness62
  | 63 => witness63
  | 64 => witness64
  | 65 => witness65
  | 66 => witness66
  | 67 => witness67
  | _ => witness0
end ThomsonNegative.Certificate.Correction.q09
