import UniformDirectLeafForestProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestData
open UniformMachine UniformTensorMonomialMachine
open UniformDirectLeafCacheReader UniformDirectLeafCacheLoopGeometry UniformDirectLeafForestModel
open UniformLocalCacheTreeMachine

structure Parameters where
 start:Config
 radix:ℕ
 nodes:ℕ
 starts:ℕ
 durations:ℕ
 forward:ℕ
 transpose:ℕ
 seedPool:ℕ
 rectangles:ℕ
 rootDuration:ℕ
 ranges:ℕ

def position (p:Parameters) (visits:List Visit) (i:ℕ):Config:=
 let j:=before visits i
 {p.start with
  record:=p.forward
  pool:=p.start.pool+9*p.radix*j
  permutation:=p.start.permutation+(3*p.radix+11)*j
  widths:=p.start.widths+(3*p.radix+11)*j
  markers:=p.start.markers+(3*p.radix+11)*j
  axis:=p.start.axis+(3*p.radix+11)*j
  entry:=p.start.entry+(3*p.radix+11)*j
  time:=0}

structure Header (p:Parameters) (visits:List Visit) (s:State):Prop where
 nodes:s.natReg 6660=p.nodes
 count:s.natReg 6661=visits.length
 starts:s.natReg 6664=p.starts
 durations:s.natReg 6665=p.durations
 original:s.natReg 6690=p.start.originalDirectory
 conjugate:s.natReg 6691=p.start.conjugateDirectory
 rows:s.natReg 6692=p.start.rows
 pool:s.natReg 6160=p.start.pool
 permutation:s.natReg 6162=p.start.permutation
 widths:s.natReg 6163=p.start.widths
 markers:s.natReg 6164=p.start.markers
 axis:s.natReg 6165=p.start.axis
 entry:s.natReg 6166=p.start.entry
 forward:s.natReg 6814=p.forward
 transpose:s.natReg 6815=p.transpose
 radix:s.natReg 6800=p.radix
 seedPool:s.natReg 6820=p.seedPool
 root:s.natHeap p.durations=some p.rootDuration
 ranges:s.natReg 6810=p.ranges

structure Core (c:Config) (s:State):Prop where
 originalDirectory:s.natReg 6601=c.originalDirectory
 conjugateDirectory:s.natReg 6602=c.conjugateDirectory
 pool:s.natReg 6603=c.pool
 rows:s.natReg 6604=c.rows
 permutation:s.natReg 6605=c.permutation
 widths:s.natReg 6606=c.widths
 markers:s.natReg 6607=c.markers
 axis:s.natReg 6608=c.axis
 entry:s.natReg 6609=c.entry

structure Cursor (p:Parameters) (visits:List Visit) (i:ℕ) (s:State):Prop extends
 Core (position p visits i) s where
 nodes:s.natReg 6660=p.nodes
 count:s.natReg 6661=visits.length
 index:s.natReg 6662=i
 pointer:s.natReg 6663=p.nodes+7*i
 starts:s.natReg 6664=p.starts
 durations:s.natReg 6665=p.durations
 root:s.natReg 6666=p.rootDuration
 one:s.natReg 6669=1
 two:s.natReg 6670=2
 seven:s.natReg 6671=7
 four:s.natReg 6672=4
 fourteen:s.natReg 6673=14
 zero:s.natReg 6679=0
 ordinal:s.natReg 6680=p.rectangles+before visits i
 divisor:s.natReg 6681=9*p.radix
 forward:s.natReg 5602=p.forward
 transpose:s.natReg 5603=p.transpose
 ranges:s.natReg 6693=p.ranges

structure ReadCursor (p:Parameters) (visits:List Visit) (i:ℕ) (q:Visit) (s:State):Prop extends
 Cursor p visits i s where
 width:s.natReg 6667=q.task.width
 selected:s.natReg 6668=UniformWorkspacePlanner.selected q.task.width
 start:s.natReg 6676=0

lemma Core.withPC {c:Config}{s:State}(h:Core c s)(pc:ℕ):Core c (setPC s pc):=by
 exact ⟨h.1,h.2,h.3,h.4,h.5,h.6,h.7,h.8,h.9⟩
lemma Cursor.withPC {p:Parameters}{visits:List Visit}{i:ℕ}{s:State}
 (h:Cursor p visits i s)(pc:ℕ):Cursor p visits i (setPC s pc):=by
 exact ⟨h.toCore.withPC pc,h.nodes,h.count,h.index,h.pointer,h.starts,h.durations,h.root,
 h.one,h.two,h.seven,h.four,h.fourteen,h.zero,h.ordinal,h.divisor,h.forward,h.transpose,h.ranges⟩
lemma ReadCursor.withPC {p:Parameters}{visits:List Visit}{i:ℕ}{q:Visit}{s:State}
 (h:ReadCursor p visits i q s)(pc:ℕ):ReadCursor p visits i q (setPC s pc):=by
 exact ⟨h.toCursor.withPC pc,h.width,h.selected,h.start⟩
end ExactFourierCircuits.UniformDirectLeafForestData
