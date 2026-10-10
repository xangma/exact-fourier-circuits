import DFTModelGlobalSectorPreparationGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section

theorem sectorCell_peak (x t : Tables.T) (R T j : ℕ)
 (hx:TablesBound x R) (ht:TablesBound t T) :
 (run sectorCell ((x,t),j)).peak≤2*(R*T)+R+T+j+1 := by
 have hl:=hx.sector (j/t.2.1.len)
 have hu:=ht.sector (j%t.2.1.len)
 have hp0:=Nat.mul_le_mul hl.2.1 hu.2.1
 have hp1:=Nat.mul_le_mul hl.2.2 ht.volume
 have hp2:=Nat.mul_le_mul hl.2.1 hu.2.2
 have hd: j/t.2.1.len≤j:=Nat.div_le_self _ _
 have hm: j%t.2.1.len≤j:=Nat.mod_le _ _
 have hb:=ht.blocks
 simp only [sectorCell,firstBlock,lastSector,firstBlocks,tailSectors,sectorTailLength,
   tailVolume,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,
   Bill.word,Ty.blank]
 dsimp only at hl hu hp0 hp1 hp2
 rcases hl with ⟨hl0,hl1,hl2⟩
 rcases hu with ⟨hu0,hu1,hu2⟩
 simp only [max_zero,zero_max]
 have hq:=Nat.add_le_add hl0 hu0
 have hs:=Nat.add_le_add hp1 hp2
 repeat' apply max_le
 all_goals first
 | exact le_trans hb (by omega)
 | exact le_trans hd (by omega)
 | exact le_trans hm (by omega)
 | exact le_trans hq (by omega)
 | exact le_trans hp0 (by omega)
 | exact le_trans hp1 (by omega)
 | exact le_trans hp2 (by omega)
 | exact le_trans hs (by omega)

theorem addressCell_peak (x t : Tables.T) (R T j : ℕ)
 (hx:TablesBound x R) (ht:TablesBound t T) :
 (run addressCell ((x,t),j)).peak≤2*(R*T)+R+T+j+1 := by
 have hl:=hx.address (j/t.2.2.len)
 have hu:=ht.address (j%t.2.2.len)
 have hp0:=Nat.mul_le_mul hl.1 hu.1
 have hp1:=Nat.mul_le_mul hl.2.1 ht.volume
 have hp2:=Nat.mul_le_mul hl.1 hu.2.1
 have hp3:=Nat.mul_le_mul hl.2.2.1 hu.1
 have hp4:=Nat.mul_le_mul hl.2.2.2 ht.volume
 have hd: j/t.2.2.len≤j:=Nat.div_le_self _ _
 have hm: j%t.2.2.len≤j:=Nat.mod_le _ _
 have hb:=ht.addresses
 simp only [addressCell,firstDigit,lastAddress,firstDigits,tailAddresses,addressTailLength,
   tailVolume,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,
   Bill.word,Ty.blank]
 dsimp only at hl hu hp0 hp1 hp2 hp3 hp4
 rcases hl with ⟨hl0,hl1,hl2,hl3⟩
 rcases hu with ⟨hu0,hu1,hu2,hu3⟩
 simp only [max_zero,zero_max]
 have hs:=Nat.add_le_add hp1 hp2
 have ho:=Nat.add_le_add hp3 hu2
 have hr:=Nat.add_le_add hp4 hu3
 repeat' apply max_le
 all_goals first
 | exact le_trans hb (by omega)
 | exact le_trans hd (by omega)
 | exact le_trans hm (by omega)
 | exact le_trans hp0 (by omega)
 | exact le_trans hp1 (by omega)
 | exact le_trans hp2 (by omega)
 | exact le_trans hp3 (by omega)
 | exact le_trans hp4 (by omega)
 | exact le_trans hs (by omega)
 | exact le_trans ho (by omega)
 | exact le_trans hr (by omega)

attribute [local irreducible] sectorCell addressCell

theorem expand_peak (x t : Tables.T) (R T : ℕ)
 (hx:TablesBound x R) (ht:TablesBound t T) :
 (run expand (x,t)).peak≤3*(R*T)+R+T+1 := by
 have hslen:=Nat.mul_le_mul hx.blocks ht.blocks
 have halen:=Nat.mul_le_mul hx.volume ht.addresses
 have hprod:=Nat.mul_le_mul hx.volume ht.volume
 have hs:(Bill.tab (x.2.1.len*t.2.1.len) Sector.blank
   (fun j=>run sectorCell ((x,t),j))).peak≤3*(R*T)+R+T+1 := by
   rw [ModelEquivalenceInterpreter.tab_peak]
   apply max_le (by omega)
   apply Finset.sup_le
   intro j hj
   have hp:=sectorCell_peak x t R T j hx ht
   have hj:=Finset.mem_range.mp hj
   omega
 have ha:(Bill.tab (x.1*t.2.2.len) Address.blank
   (fun j=>run addressCell ((x,t),j))).peak≤3*(R*T)+R+T+1 := by
   rw [ModelEquivalenceInterpreter.tab_peak]
   apply max_le (by omega)
   apply Finset.sup_le
   intro j hj
   have hp:=addressCell_peak x t R T j hx ht
   have hj:=Finset.mem_range.mp hj
   omega
 have xb:=hx.blocks
 have tb:=ht.blocks
 have tv:=ht.volume
 have xv:=hx.volume
 have ta:=ht.addresses
 simp only [expand,sectorLength,addressLength,firstRadix,firstBlocks,tailSectors,
   tailAddresses,tailVolume,nat,run,Code.run,Atom.run,NOp.run,
   Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
 norm_num
 dsimp only [run,Ty.blank] at hs ha
 omega

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
