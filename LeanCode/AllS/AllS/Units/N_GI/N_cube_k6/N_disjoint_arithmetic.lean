import AllS.Units.N_GI.N_cube_k6.N_symmetry

set_option maxHeartbeats 30000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

/-- Exact finite linear incidence contradiction for the two disjoint triangles.
The two degree-four vertices are x,y; labels0..2 and3..5 are the triangles.
The matrices are zero-one adjacency indicators, with no graph enumeration. -/
theorem disjoint_triangles_incidence_normalized_impossible (g d : Fin 8 → Fin 8 → ℕ)
    (x y : Fin 8) (hcase : (x=0 ∧ y=1) ∨ (x=0 ∧ y=3) ∨ (x=0 ∧ y=6) ∨ (x=6 ∧ y=7))
    (hgdiag : ∀i,g i i=0) (hddiag : ∀i,d i i=0)
    (hgsymm : ∀i j,g i j=g j i) (hdsymm : ∀i j,d i j=d j i)
    (hdisjoint : ∀i j,g i j+d i j≤1)
    (hgdegree : ∀i,(∑j,g i j)=if i=x ∨ i=y then 4 else 3)
    (hddegree : ∀i,(∑j,d i j)=if i=x ∨ i=y then (if i.val<6 then 3 else 4)
      else (if i.val<6 then 2 else 3))
    (htri : g 0 1=1 ∧ g 0 2=1 ∧ g 1 2=1 ∧ g 3 4=1 ∧ g 3 5=1 ∧ g 4 5=1)
    (hmixed : ∀i j,(i=x ∨ i=y) → j≠x → j≠y → j.val<6 → d i j=0) : False := by
  obtain ⟨h01,h02,h12,h34,h35,h45⟩ := htri
  have hgdiag0 := hgdiag 0
  have hddiag0 := hddiag 0
  have hgr0 := hgdegree 0
  have hdr0 := hddegree 0
  have hgdiag1 := hgdiag 1
  have hddiag1 := hddiag 1
  have hgr1 := hgdegree 1
  have hdr1 := hddegree 1
  have hgdiag2 := hgdiag 2
  have hddiag2 := hddiag 2
  have hgr2 := hgdegree 2
  have hdr2 := hddegree 2
  have hgdiag3 := hgdiag 3
  have hddiag3 := hddiag 3
  have hgr3 := hgdegree 3
  have hdr3 := hddegree 3
  have hgdiag4 := hgdiag 4
  have hddiag4 := hddiag 4
  have hgr4 := hgdegree 4
  have hdr4 := hddegree 4
  have hgdiag5 := hgdiag 5
  have hddiag5 := hddiag 5
  have hgr5 := hgdegree 5
  have hdr5 := hddegree 5
  have hgdiag6 := hgdiag 6
  have hddiag6 := hddiag 6
  have hgr6 := hgdegree 6
  have hdr6 := hddegree 6
  have hgdiag7 := hgdiag 7
  have hddiag7 := hddiag 7
  have hgr7 := hgdegree 7
  have hdr7 := hddegree 7
  have hgs01 := hgsymm 0 1
  have hds01 := hdsymm 0 1
  have hgd01 := hdisjoint 0 1
  have hgs02 := hgsymm 0 2
  have hds02 := hdsymm 0 2
  have hgd02 := hdisjoint 0 2
  have hgs03 := hgsymm 0 3
  have hds03 := hdsymm 0 3
  have hgd03 := hdisjoint 0 3
  have hgs04 := hgsymm 0 4
  have hds04 := hdsymm 0 4
  have hgd04 := hdisjoint 0 4
  have hgs05 := hgsymm 0 5
  have hds05 := hdsymm 0 5
  have hgd05 := hdisjoint 0 5
  have hgs06 := hgsymm 0 6
  have hds06 := hdsymm 0 6
  have hgd06 := hdisjoint 0 6
  have hgs07 := hgsymm 0 7
  have hds07 := hdsymm 0 7
  have hgd07 := hdisjoint 0 7
  have hgs12 := hgsymm 1 2
  have hds12 := hdsymm 1 2
  have hgd12 := hdisjoint 1 2
  have hgs13 := hgsymm 1 3
  have hds13 := hdsymm 1 3
  have hgd13 := hdisjoint 1 3
  have hgs14 := hgsymm 1 4
  have hds14 := hdsymm 1 4
  have hgd14 := hdisjoint 1 4
  have hgs15 := hgsymm 1 5
  have hds15 := hdsymm 1 5
  have hgd15 := hdisjoint 1 5
  have hgs16 := hgsymm 1 6
  have hds16 := hdsymm 1 6
  have hgd16 := hdisjoint 1 6
  have hgs17 := hgsymm 1 7
  have hds17 := hdsymm 1 7
  have hgd17 := hdisjoint 1 7
  have hgs23 := hgsymm 2 3
  have hds23 := hdsymm 2 3
  have hgd23 := hdisjoint 2 3
  have hgs24 := hgsymm 2 4
  have hds24 := hdsymm 2 4
  have hgd24 := hdisjoint 2 4
  have hgs25 := hgsymm 2 5
  have hds25 := hdsymm 2 5
  have hgd25 := hdisjoint 2 5
  have hgs26 := hgsymm 2 6
  have hds26 := hdsymm 2 6
  have hgd26 := hdisjoint 2 6
  have hgs27 := hgsymm 2 7
  have hds27 := hdsymm 2 7
  have hgd27 := hdisjoint 2 7
  have hgs34 := hgsymm 3 4
  have hds34 := hdsymm 3 4
  have hgd34 := hdisjoint 3 4
  have hgs35 := hgsymm 3 5
  have hds35 := hdsymm 3 5
  have hgd35 := hdisjoint 3 5
  have hgs36 := hgsymm 3 6
  have hds36 := hdsymm 3 6
  have hgd36 := hdisjoint 3 6
  have hgs37 := hgsymm 3 7
  have hds37 := hdsymm 3 7
  have hgd37 := hdisjoint 3 7
  have hgs45 := hgsymm 4 5
  have hds45 := hdsymm 4 5
  have hgd45 := hdisjoint 4 5
  have hgs46 := hgsymm 4 6
  have hds46 := hdsymm 4 6
  have hgd46 := hdisjoint 4 6
  have hgs47 := hgsymm 4 7
  have hds47 := hdsymm 4 7
  have hgd47 := hdisjoint 4 7
  have hgs56 := hgsymm 5 6
  have hds56 := hdsymm 5 6
  have hgd56 := hdisjoint 5 6
  have hgs57 := hgsymm 5 7
  have hds57 := hdsymm 5 7
  have hgd57 := hdisjoint 5 7
  have hgs67 := hgsymm 6 7
  have hds67 := hdsymm 6 7
  have hgd67 := hdisjoint 6 7
  have hm01 := hmixed 0 1
  have hm02 := hmixed 0 2
  have hm03 := hmixed 0 3
  have hm04 := hmixed 0 4
  have hm05 := hmixed 0 5
  have hm10 := hmixed 1 0
  have hm12 := hmixed 1 2
  have hm13 := hmixed 1 3
  have hm14 := hmixed 1 4
  have hm15 := hmixed 1 5
  have hm20 := hmixed 2 0
  have hm21 := hmixed 2 1
  have hm23 := hmixed 2 3
  have hm24 := hmixed 2 4
  have hm25 := hmixed 2 5
  have hm30 := hmixed 3 0
  have hm31 := hmixed 3 1
  have hm32 := hmixed 3 2
  have hm34 := hmixed 3 4
  have hm35 := hmixed 3 5
  have hm40 := hmixed 4 0
  have hm41 := hmixed 4 1
  have hm42 := hmixed 4 2
  have hm43 := hmixed 4 3
  have hm45 := hmixed 4 5
  have hm50 := hmixed 5 0
  have hm51 := hmixed 5 1
  have hm52 := hmixed 5 2
  have hm53 := hmixed 5 3
  have hm54 := hmixed 5 4
  have hm60 := hmixed 6 0
  have hm61 := hmixed 6 1
  have hm62 := hmixed 6 2
  have hm63 := hmixed 6 3
  have hm64 := hmixed 6 4
  have hm65 := hmixed 6 5
  have hm70 := hmixed 7 0
  have hm71 := hmixed 7 1
  have hm72 := hmixed 7 2
  have hm73 := hmixed 7 3
  have hm74 := hmixed 7 4
  have hm75 := hmixed 7 5
  clear hgdiag hddiag hgsymm hdsymm hdisjoint hgdegree hddegree hmixed
  rcases hcase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  ·
    clear hgdiag0 hgr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgs02 hds02 hgd02 hgs03 hds03 hgd03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgs07 hds07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h02 h12 h34 h35 h45
    norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
    omega
  ·
    have hD0 : d 0 3=1 ∧ d 0 6=1 ∧ d 0 7=1 := by
      clear hgdiag0 hgr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hds03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgs07 hds07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm03 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 h45
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    have hD3 : d 3 0=1 ∧ d 3 6=1 ∧ d 3 7=1 := by
      clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hgr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgd06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgs37 hds37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 h45 hD0
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    have hG0 : g 0 3=0 ∧ g 0 6=0 ∧ g 0 7=0 := by
      clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hds03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgs07 hds07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 h45 hD3
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    have hG3 : g 3 0=0 ∧ g 3 6=0 ∧ g 3 7=0 := by
      clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgd06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgs37 hds37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 h45 hD0 hG0
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    have hA0 : g 0 1=1 ∧ g 0 2=1 ∧ g 0 4=1 ∧ g 0 5=1 := by
      clear hddiag0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgs02 hds02 hgs03 hds03 hgd03 hgs04 hds04 hgs05 hds05 hgs06 hds06 hgd06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 h45 hD0 hD3 hG3
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    have hA3 : g 3 1=1 ∧ g 3 2=1 ∧ g 3 4=1 ∧ g 3 5=1 := by
      clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hddiag3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hds03 hgd03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgd06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hds13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hds23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgs35 hds35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 h45 hD0 hD3 hG0 hA0
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    have hH1 : g 1 6=0 ∧ g 1 7=0 := by
      clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hds03 hgd03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgd06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h34 h35 h45 hD0 hD3 hG0 hG3
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    have hH2 : g 2 6=0 ∧ g 2 7=0 := by
      clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hds02 hgd02 hgs03 hds03 hgd03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgd06 hgs07 hds07 hgd07 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h34 h35 h45 hD0 hD3 hG0 hG3 hH1
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    have hH4 : g 4 6=0 ∧ g 4 7=0 := by
      clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hds03 hgd03 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgd06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 hD0 hD3 hG0 hG3 hH1 hH2
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    have hH5 : g 5 6=0 ∧ g 5 7=0 := by
      clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hdr5 hgdiag6 hddiag6 hgr6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hds03 hgd03 hgs04 hds04 hgd04 hds05 hgd05 hgs06 hds06 hgd06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hgd67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 hD0 hD3 hG0 hG3 hH1 hH2 hH4
      norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
      omega
    clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hddiag6 hdr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hds03 hgd03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hds06 hgd06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hds46 hgd46 hgs47 hds47 hgd47 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm61 hm62 hm63 hm64 hm65 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 h45 hD0 hD3 hA0 hA3
    norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
    omega
  ·
    clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hgr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hds03 hgd03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm60 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 h45
    norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
    omega
  ·
    clear hgdiag0 hddiag0 hgr0 hdr0 hgdiag1 hddiag1 hgr1 hdr1 hgdiag2 hddiag2 hgr2 hdr2 hgdiag3 hddiag3 hgr3 hdr3 hgdiag4 hddiag4 hgr4 hdr4 hgdiag5 hddiag5 hgr5 hdr5 hgdiag6 hgr6 hgdiag7 hddiag7 hgr7 hdr7 hgs01 hds01 hgd01 hgs02 hds02 hgd02 hgs03 hds03 hgd03 hgs04 hds04 hgd04 hgs05 hds05 hgd05 hgs06 hds06 hgd06 hgs07 hds07 hgd07 hgs12 hds12 hgd12 hgs13 hds13 hgd13 hgs14 hds14 hgd14 hgs15 hds15 hgd15 hgs16 hds16 hgd16 hgs17 hds17 hgd17 hgs23 hds23 hgd23 hgs24 hds24 hgd24 hgs25 hds25 hgd25 hgs26 hds26 hgd26 hgs27 hds27 hgd27 hgs34 hds34 hgd34 hgs35 hds35 hgd35 hgs36 hds36 hgd36 hgs37 hds37 hgd37 hgs45 hds45 hgd45 hgs46 hds46 hgd46 hgs47 hds47 hgd47 hgs56 hds56 hgd56 hgs57 hds57 hgd57 hgs67 hds67 hm01 hm02 hm03 hm04 hm05 hm10 hm12 hm13 hm14 hm15 hm20 hm21 hm23 hm24 hm25 hm30 hm31 hm32 hm34 hm35 hm40 hm41 hm42 hm43 hm45 hm50 hm51 hm52 hm53 hm54 hm70 hm71 hm72 hm73 hm74 hm75 h01 h02 h12 h34 h35 h45
    norm_num [Fin.sum_univ_eight,Fin.ext_iff] at *
    omega

theorem disjoint_triangles_incidence_impossible (g d : Fin 8 → Fin 8 → ℕ)
    (x y : Fin 8) (hxy : x≠y)
    (hgdiag : ∀i,g i i=0) (hddiag : ∀i,d i i=0)
    (hgsymm : ∀i j,g i j=g j i) (hdsymm : ∀i j,d i j=d j i)
    (hdisjoint : ∀i j,g i j+d i j≤1)
    (hgdegree : ∀i,(∑j,g i j)=if i=x ∨ i=y then 4 else 3)
    (hddegree : ∀i,(∑j,d i j)=if i=x ∨ i=y then (if i.val<6 then 3 else 4)
      else (if i.val<6 then 2 else 3))
    (htri : ∀i j,i≠j → sameTriangleIndex i j → g i j=1)
    (hmixed : ∀i j,(i=x ∨ i=y) → j≠x → j≠y → j.val<6 → d i j=0) : False := by
  obtain ⟨e,a,b,hcase,hL,hI,hT⟩ := triangle_pair_normalization x y hxy
  apply disjoint_triangles_incidence_normalized_impossible
    (fun i j => g (e i) (e j)) (fun i j => d (e i) (e j)) a b hcase
    (fun i => hgdiag (e i)) (fun i => hddiag (e i))
    (fun i j => hgsymm (e i) (e j)) (fun i j => hdsymm (e i) (e j))
    (fun i j => hdisjoint (e i) (e j))
  · intro i
    rw [Equiv.sum_comp e (g (e i)),hgdegree]
    exact if_congr (hL i) rfl rfl
  · intro i
    rw [Equiv.sum_comp e (d (e i)),hddegree]
    simp only [hL i,hI i]
  · have he (i j : Fin 8) (hij : i≠j) (ht : sameTriangleIndex i j) : g (e i) (e j)=1 :=
      htri (e i) (e j) (e.injective.ne hij) ((hT i j).mpr ht)
    exact ⟨he 0 1 (by decide) (by decide),he 0 2 (by decide) (by decide),
      he 1 2 (by decide) (by decide),he 3 4 (by decide) (by decide),
      he 3 5 (by decide) (by decide),he 4 5 (by decide) (by decide)⟩
  · intro i j hi hja hjb hj
    have hn : ¬(e j=x ∨ e j=y) := fun h => ((hL j).mp h).elim hja hjb
    exact hmixed (e i) (e j) ((hL i).mpr hi) (fun h => hn (Or.inl h))
      (fun h => hn (Or.inr h)) ((hI j).mpr hj)

#print axioms disjoint_triangles_incidence_impossible
#print axioms disjoint_triangles_incidence_normalized_impossible
end Blueprint.Thomson.Tail.Implementation
