import UniformJointCacheWorkspace
import UniformLocalCacheSlotGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalCacheSlotGeometry
open UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformLocalCacheSlotConductorMachine
namespace W
abbrev original:=UniformJointCacheWorkspace.original
abbrev stride:=UniformJointCacheWorkspace.stride
end W
noncomputable section

def context (constants : Constants) (n : ℕ) (axisIndex : Fin (axisCount n))
 (q : Row) (k time : ℕ) : Header.Parameters :=
 let a:=UniformJointCacheAllocation.axis constants n axisIndex
 let b:=UniformJointCacheAllocation.slot a k
 let z:=W.stride n
 {height:=(W.original n q).height
  falseRows:=18*z
  falseColors:=19*z
  falsePalette:=20*z
  falseDirectory:=21*z
  gates:=(W.original n q).gates
  negative:=5*z
  conjugates:=11*z
  rectangle:=z
  slot:=17*z
  borrowed:=23*z
  selected:=24*z
  ordinals:=25*z
  mapped:=26*z
  permutation:=27*z
  widths:=28*z
  markers:=29*z
  axis:=30*z
  translated:=31*z
  pool:=b.factor
  ambient:=radix n axisIndex
  mu:=22*z
  conjugateMu:=22*z+1
  time:=time
  cachePermutation:=b.permutation
  cacheWidths:=b.widths
  cacheMarkers:=b.markers
  cacheAxis:=b.physicalAxis
  cacheDirectory:=b.abi
  kind:=0}

end
end ExactFourierCircuits.UniformCanonicalCacheSlotGeometry
