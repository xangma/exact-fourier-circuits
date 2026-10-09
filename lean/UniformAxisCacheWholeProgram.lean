import UniformAxisCacheBootInputs
import UniformAxisCacheForestHeader
import UniformAxisCacheTail
import UniformLocalStoredRequestLoopProgram
import UniformDirectLeafForestProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheWholeProgram
open UniformMachine UniformAssembly

def resetCode:Program:=UniformAxisCacheBoot.resetOps.map UniformNatBlockMachine.Op.code
def startupCode:Program:=UniformAxisCacheStartupMachine.program.map (relocate 1 18)
def saveCode:Program:=UniformAxisCacheBootInputs.save.map UniformNatBlockMachine.Op.code
def prepareCode:Program:=UniformAxisCacheTimingProgram.program.map (relocate 20 390)
def horizonCode:Program:=UniformGlobalClockHorizon.block.map UniformTensorMonomialMachine.Op.code
def headerCode:Program:=UniformAxisCacheForestHeader.ops.map UniformNatBlockMachine.Op.code
def requestCode:Program:=UniformLocalStoredRequestLoop.program.map (relocate 405 4181)
def forestCode:Program:=UniformDirectLeafForestProgram.program.map (relocate 4181 4642)
def tailCode:Program:=UniformAxisCacheLoopTail.program.map (relocate 4642 0)
def advanceCode:Program:=UniformAxisCacheAdvanceMachine.program.map (relocate 4644 20)
def body:Program:=resetCode++startupCode++saveCode++prepareCode++horizonCode++headerCode++requestCode++forestCode++tailCode++advanceCode
/-- One fixed program for every axis: executed boot, forest/timing producer,
maximum clock, immutable leaf header, all requests, forward leaves, then a real
advance/backedge or final halt. -/
def program:Program:=body++[.halt]

lemma resetCode_length:resetCode.length=1:=rfl
lemma startupCode_length:startupCode.length=17:=by simp only [startupCode,List.length_map,UniformAxisCacheStartupMachine.program_length]
lemma saveCode_length:saveCode.length=2:=by simp only [saveCode,List.length_map,UniformAxisCacheBootInputs.save_length]
lemma prepareCode_length:prepareCode.length=370:=by simp only [prepareCode,List.length_map,UniformAxisCacheTimingProgram.program_length]
lemma horizonCode_length:horizonCode.length=7:=by simp only [horizonCode,List.length_map,UniformGlobalClockHorizon.block_length]
lemma headerCode_length:headerCode.length=8:=by simp only [headerCode,List.length_map,UniformAxisCacheForestHeader.ops_length]
lemma requestCode_length:requestCode.length=3776:=by simp only [requestCode,List.length_map,UniformLocalStoredRequestLoop.program_length]
lemma forestCode_length:forestCode.length=461:=by simp only [forestCode,List.length_map,UniformDirectLeafForestProgram.program_length]
lemma tailCode_length:tailCode.length=2:=by simp only [tailCode,List.length_map,UniformAxisCacheLoopTail.program_length]
lemma advanceCode_length:advanceCode.length=9:=by simp only [advanceCode,List.length_map,UniformAxisCacheAdvanceMachine.program_length]
lemma body_length:body.length=4653:=by simp only [body,List.length_append,resetCode_length,startupCode_length,saveCode_length,prepareCode_length,horizonCode_length,headerCode_length,requestCode_length,forestCode_length,tailCode_length,advanceCode_length]
lemma program_length:program.length=4654:=by simp only [program,List.length_append,body_length,List.length_singleton]

lemma nat_segment (head suffix:Program) (os:List UniformNatBlockMachine.Op) (base:ℕ)
 (length:head.length=base):UniformNatBlockMachine.BlockAt os (head++os.map UniformNatBlockMachine.Op.code++suffix) base:=by
 intro i hi
 have item:=UniformAllAxisSeedPreparation.lookup_segment head (os.map UniformNatBlockMachine.Op.code) suffix i
  (by simpa only [List.length_map] using hi)
 simpa only [length,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using item
lemma tensor_segment (head suffix:Program) (os:List UniformTensorMonomialMachine.Op) (base:ℕ)
 (length:head.length=base):UniformTensorMonomialMachine.BlockAt os (head++os.map UniformTensorMonomialMachine.Op.code++suffix) base:=by
 intro i hi
 have item:=UniformAllAxisSeedPreparation.lookup_segment head (os.map UniformTensorMonomialMachine.Op.code) suffix i
  (by simpa only [List.length_map] using hi)
 simpa only [length,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using item

attribute [local irreducible] UniformAxisCacheStartupMachine.program UniformAxisCacheTimingProgram.program UniformLocalStoredRequestLoop.program UniformDirectLeafForestProgram.program UniformAxisCacheLoopTail.program UniformAxisCacheAdvanceMachine.program

lemma resetCode_at:UniformNatBlockMachine.BlockAt UniformAxisCacheBoot.resetOps program 0:=by
 let before:Program:=[]
 let after:Program:=startupCode++saveCode++prepareCode++horizonCode++headerCode++requestCode++forestCode++tailCode++advanceCode++[.halt]
 have length:before.length=0:=rfl
 have shape:program=before++(UniformAxisCacheBoot.resetOps.map UniformNatBlockMachine.Op.code)++after:=by
  simp only [program,body,before,after,resetCode,List.nil_append,List.append_assoc]
 rw [shape]
 exact nat_segment before after UniformAxisCacheBoot.resetOps 0 length

lemma startupCode_at:CodeAt UniformAxisCacheStartupMachine.program program 1 18:=by
 let before:Program:=resetCode
 let after:Program:=saveCode++prepareCode++horizonCode++headerCode++requestCode++forestCode++tailCode++advanceCode++[.halt]
 have length:before.length=1:=by simp only [before,resetCode_length]
 have shape:program=before++(UniformAxisCacheStartupMachine.program.map (relocate 1 18))++after:=by
  simp only [program,body,before,after,startupCode,List.append_assoc]
 rw [shape]
 exact UniformRankCrossPreparationMachine.segment_code before after UniformAxisCacheStartupMachine.program 1 18 length

lemma saveCode_at:UniformNatBlockMachine.BlockAt UniformAxisCacheBootInputs.save program 18:=by
 let before:Program:=resetCode++startupCode
 let after:Program:=prepareCode++horizonCode++headerCode++requestCode++forestCode++tailCode++advanceCode++[.halt]
 have length:before.length=18:=by simp only [before,List.length_append,resetCode_length,startupCode_length]
 have shape:program=before++(UniformAxisCacheBootInputs.save.map UniformNatBlockMachine.Op.code)++after:=by
  simp only [program,body,before,after,saveCode,List.append_assoc]
 rw [shape]
 exact nat_segment before after UniformAxisCacheBootInputs.save 18 length

lemma prepareCode_at:CodeAt UniformAxisCacheTimingProgram.program program 20 390:=by
 let before:Program:=resetCode++startupCode++saveCode
 let after:Program:=horizonCode++headerCode++requestCode++forestCode++tailCode++advanceCode++[.halt]
 have length:before.length=20:=by simp only [before,List.length_append,resetCode_length,startupCode_length,saveCode_length]
 have shape:program=before++(UniformAxisCacheTimingProgram.program.map (relocate 20 390))++after:=by
  simp only [program,body,before,after,prepareCode,List.append_assoc]
 rw [shape]
 exact UniformRankCrossPreparationMachine.segment_code before after UniformAxisCacheTimingProgram.program 20 390 length

lemma horizonCode_at:UniformTensorMonomialMachine.BlockAt UniformGlobalClockHorizon.block program 390:=by
 let before:Program:=resetCode++startupCode++saveCode++prepareCode
 let after:Program:=headerCode++requestCode++forestCode++tailCode++advanceCode++[.halt]
 have length:before.length=390:=by simp only [before,List.length_append,resetCode_length,startupCode_length,saveCode_length,prepareCode_length]
 have shape:program=before++(UniformGlobalClockHorizon.block.map UniformTensorMonomialMachine.Op.code)++after:=by
  simp only [program,body,before,after,horizonCode,List.append_assoc]
 rw [shape]
 exact tensor_segment before after UniformGlobalClockHorizon.block 390 length

lemma headerCode_at:UniformNatBlockMachine.BlockAt UniformAxisCacheForestHeader.ops program 397:=by
 let before:Program:=resetCode++startupCode++saveCode++prepareCode++horizonCode
 let after:Program:=requestCode++forestCode++tailCode++advanceCode++[.halt]
 have length:before.length=397:=by simp only [before,List.length_append,resetCode_length,startupCode_length,saveCode_length,prepareCode_length,horizonCode_length]
 have shape:program=before++(UniformAxisCacheForestHeader.ops.map UniformNatBlockMachine.Op.code)++after:=by
  simp only [program,body,before,after,headerCode,List.append_assoc]
 rw [shape]
 exact nat_segment before after UniformAxisCacheForestHeader.ops 397 length

lemma requestCode_at:CodeAt UniformLocalStoredRequestLoop.program program 405 4181:=by
 let before:Program:=resetCode++startupCode++saveCode++prepareCode++horizonCode++headerCode
 let after:Program:=forestCode++tailCode++advanceCode++[.halt]
 have length:before.length=405:=by simp only [before,List.length_append,resetCode_length,startupCode_length,saveCode_length,prepareCode_length,horizonCode_length,headerCode_length]
 have shape:program=before++(UniformLocalStoredRequestLoop.program.map (relocate 405 4181))++after:=by
  simp only [program,body,before,after,requestCode,List.append_assoc]
 rw [shape]
 exact UniformRankCrossPreparationMachine.segment_code before after UniformLocalStoredRequestLoop.program 405 4181 length

lemma forestCode_at:CodeAt UniformDirectLeafForestProgram.program program 4181 4642:=by
 let before:Program:=resetCode++startupCode++saveCode++prepareCode++horizonCode++headerCode++requestCode
 let after:Program:=tailCode++advanceCode++[.halt]
 have length:before.length=4181:=by simp only [before,List.length_append,resetCode_length,startupCode_length,saveCode_length,prepareCode_length,horizonCode_length,headerCode_length,requestCode_length]
 have shape:program=before++(UniformDirectLeafForestProgram.program.map (relocate 4181 4642))++after:=by
  simp only [program,body,before,after,forestCode,List.append_assoc]
 rw [shape]
 exact UniformRankCrossPreparationMachine.segment_code before after UniformDirectLeafForestProgram.program 4181 4642 length

lemma tailCode_at:CodeAt UniformAxisCacheLoopTail.program program 4642 0:=by
 let before:Program:=resetCode++startupCode++saveCode++prepareCode++horizonCode++headerCode++requestCode++forestCode
 let after:Program:=advanceCode++[.halt]
 have length:before.length=4642:=by simp only [before,List.length_append,resetCode_length,startupCode_length,saveCode_length,prepareCode_length,horizonCode_length,headerCode_length,requestCode_length,forestCode_length]
 have shape:program=before++(UniformAxisCacheLoopTail.program.map (relocate 4642 0))++after:=by
  simp only [program,body,before,after,tailCode,List.append_assoc]
 rw [shape]
 exact UniformRankCrossPreparationMachine.segment_code before after UniformAxisCacheLoopTail.program 4642 0 length

lemma advanceCode_at:CodeAt UniformAxisCacheAdvanceMachine.program program 4644 20:=by
 let before:Program:=resetCode++startupCode++saveCode++prepareCode++horizonCode++headerCode++requestCode++forestCode++tailCode
 let after:Program:=[.halt]
 have length:before.length=4644:=by simp only [before,List.length_append,resetCode_length,startupCode_length,saveCode_length,prepareCode_length,horizonCode_length,headerCode_length,requestCode_length,forestCode_length,tailCode_length]
 have shape:program=before++(UniformAxisCacheAdvanceMachine.program.map (relocate 4644 20))++after:=by
  simp only [program,body,before,after,advanceCode,List.append_assoc]
 rw [shape]
 exact UniformRankCrossPreparationMachine.segment_code before after UniformAxisCacheAdvanceMachine.program 4644 20 length

lemma halt_at:program[4653]?=some .halt:=by
 rw [program,List.getElem?_append_right (by rw [body_length]),body_length]
 rfl

end ExactFourierCircuits.UniformAxisCacheWholeProgram
