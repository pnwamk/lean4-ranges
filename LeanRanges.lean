import AssertCmd
import LeanRanges.ToRange
import LeanRanges.NatRange
import LeanRanges.IntRange
import LeanRanges.FinRange
import LeanRanges.UInt8Range

#check [0⋯5]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
#assert [⋯(4:Nat)].toArray  == #[0,1,2,3]
#assert [(0:Nat)⋯4].toArray  == #[0,1,2,3]
#assert [⋯=(4:Nat)].toArray  == #[0,1,2,3,4]
#assert [(0:Nat)⋯=4].toArray  == #[0,1,2,3,4]

#assert [⋯(4:Nat); -1].toArray  == #[3,2,1,0]
#assert [(0:Nat)⋯4; -1].toArray  == #[3,2,1,0]
#assert [⋯=(4:Nat); -1].toArray  == #[4,3,2,1,0]
#assert [(0:Nat)⋯=4; -1].toArray  == #[4,3,2,1,0]

#assert [⋯(4:Nat); 2].toArray  == #[0,2]
#assert [(0:Nat)⋯4; 2].toArray  == #[0,2]
#assert [⋯=(4:Nat); 2].toArray  == #[0,2,4]
#assert [(0:Nat)⋯=4; 2].toArray  == #[0,2,4]

#assert [(1:Nat)⋯4; 2].toArray  == #[1,3]
#assert [(1:Nat)⋯=4; 2].toArray  == #[1,3]

#assert [⋯(4:Nat); 3].toArray  == #[0,3]
#assert [(0:Nat)⋯4; 3].toArray  == #[0,3]
#assert [⋯=(4:Nat); 3].toArray  == #[0,3]
#assert [(0:Nat)⋯=4; 3].toArray  == #[0,3]


#assert [⋯(4:Nat); 4].toArray  == #[0]
#assert [(0:Nat)⋯4; 4].toArray  == #[0]
#assert [⋯=(4:Nat); 4].toArray  == #[0,4]
#assert [(0:Nat)⋯=4; 4].toArray  == #[0,4]

#assert [⋯(4:Nat); -4].toArray  == #[0]
#assert [(0:Nat)⋯4; -4].toArray  == #[0]
#assert [⋯=(4:Nat); -4].toArray  == #[4,0]
#assert [(0:Nat)⋯=4; -4].toArray  == #[4,0]


#assert [⋯(4:Nat); 5].toArray  == #[0]
#assert [(0:Nat)⋯4; 5].toArray  == #[0]
#assert [⋯=(4:Nat); 5].toArray  == #[0]
#assert [(0:Nat)⋯=4; 5].toArray  == #[0]

#assert [⋯(4:Nat); 0].toArray  == #[]
#assert [⋯=(4:Nat); 0].toArray  == #[]

#assert [(4:Nat)⋯0].toArray  == #[]
#assert [(4:Nat)⋯=0].toArray  == #[]

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Int
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
#assert [(-2:Int)⋯3].toArray == #[-2,-1,0,1,2]
#assert [(-2:Int)⋯=3].toArray == #[-2,-1,0,1,2,3]

#assert [(-2:Int)⋯3; 2].toArray  == #[-2, 0, 2]
#assert [(-2:Int)⋯4; 2].toArray == #[-2, 0, 2]
#assert [(-2:Int)⋯=3; 2].toArray  == #[-2, 0, 2]
#assert [(-2:Int)⋯=4; 2].toArray  == #[-2, 0, 2, 4]

#assert [(-2:Int)⋯3; -1].toArray == #[2, 1, 0, -1, -2]
#assert [(-2:Int)⋯=3; -1].toArray == #[3, 2, 1, 0, -1, -2]
#assert [(-2:Int)⋯3; -2].toArray == #[2, 0, -2]
#assert [(-2:Int)⋯4; -2].toArray == #[2, 0, -2]
#assert [(-2:Int)⋯=3; -2].toArray == #[2, 0, -2]
#assert [(-2:Int)⋯=4; -2].toArray == #[4, 2, 0, -2]

#assert [0⋯(4:Int); 0].toArray  == #[]
#assert [0⋯=(4:Int); 0].toArray  == #[]

#assert [(4:Int)⋯0].toArray  == #[]
#assert [(4:Int)⋯=0].toArray  == #[]
#assert [(-4:Int)⋯=-5].toArray  == #[]

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
#assert [(0:Fin 6)⋯4].toArray  == (#[0,1,2,3] : Array (Fin 6))
#assert [(0:Fin 6)⋯=4].toArray  == (#[0,1,2,3,4] : Array (Fin 6))
#assert (Fin.range 0 4).toArray == (#[0,1,2,3] : Array (Fin 4))
#assert (Fin.rangeEq 0 4).toArray == (#[0,1,2,3,4] : Array (Fin 5))

#assert [(0:Fin 6)⋯4; 2].toArray  == (#[0,2] : Array (Fin 6))
#assert [(0:Fin 6)⋯=4; 2].toArray  == (#[0,2,4] : Array (Fin 6))
#assert [(0:Fin 256)⋯5; 2].toArray  == (#[0,2,4] : Array (Fin 256))
#assert [(0:Fin 256)⋯=5; 2].toArray  == (#[0,2,4] : Array (Fin 256))
#assert (Fin.range (n := 3) 0 5).toArray == (#[0,1,2]: Array (Fin 3))
#assert (Fin.range (n := 5) 0 5).toArray == (#[0,1,2,3,4]: Array (Fin 5))
#assert (Fin.range (n := 10) 0 5).toArray == (#[0,1,2,3,4]: Array (Fin 10))
#assert (Fin.range 0 4 2).toArray == (#[0,2]: Array (Fin 4))
#assert (Fin.range (n := 10) 0 4 2).toArray == (#[0,2]: Array (Fin 10))
#assert (Fin.rangeEq 0 4 2).toArray == (#[0,2,4] : Array (Fin 5))
#assert (Fin.range 0 5 2).toArray == (#[0,2,4]: Array (Fin 5))
#assert (Fin.rangeEq 0 5 2).toArray == (#[0,2,4] : Array (Fin 6))
#assert (Fin.rangeEq (n := 3) 0 5 2).toArray == (#[0,2] : Array (Fin 3))
#assert (Fin.rangeEq (n := 5) 0 5 2).toArray == (#[0,2,4] : Array (Fin 5))
#assert (Fin.rangeEq (n := 10) 0 5 2).toArray == (#[0,2,4] : Array (Fin 10))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- UInt8
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
#assert [(0:UInt8)⋯5].toArray  == (#[0,1,2,3,4] : Array UInt8)
#assert [(0:UInt8)⋯=5].toArray  == (#[0,1,2,3,4,5] : Array UInt8)
#assert [(0:UInt8)⋯255].toArray.size == 255
#assert ([(0:UInt8)⋯255].toArray.get! 0) == (0 : UInt8)
#assert ([(0:UInt8)⋯255].toArray.get! 254) == (254 : UInt8)
#assert [(0:UInt8)⋯=255].toArray.size == 256
#assert ([(0:UInt8)⋯=255].toArray.get! 0) == (0 : UInt8)
#assert ([(0:UInt8)⋯=255].toArray.get! 255) == (255 : UInt8)
#assert ([(0:UInt8)⋯=255; -1].toArray.get! 0) == (255 : UInt8)
#assert ([(0:UInt8)⋯=255; -1].toArray.get! 255) == (0 : UInt8)


#assert [(0:UInt8)⋯5; 2].toArray  == (#[0,2,4] : Array UInt8)
#assert [(0:UInt8)⋯=5; 2].toArray  == (#[0,2,4] : Array UInt8)
#assert [(0:UInt8)⋯6; 2].toArray  == (#[0,2,4] : Array UInt8)
#assert [(0:UInt8)⋯=6; 2].toArray  == (#[0,2,4,6] : Array UInt8)
#assert [(0:UInt8)⋯255; 2].toArray.size == 128
#assert [(0:UInt8)⋯254; 2].toArray.size == 127
#assert ([(0:UInt8)⋯255; 2].toArray.get! 0) == (0 : UInt8)
#assert ([(0:UInt8)⋯255; 2].toArray.get! 127) == (254 : UInt8)
#assert [(0:UInt8)⋯=255; 2].toArray.size == 128
#assert [(0:UInt8)⋯=254; 2].toArray.size == 128
#assert ([(0:UInt8)⋯=255; 2].toArray.get! 0) == (0 : UInt8)
#assert ([(0:UInt8)⋯=255; 2].toArray.get! 0) == (0 : UInt8)
#assert ([(0:UInt8)⋯=254; 2].toArray.get! 0) == (0 : UInt8)
#assert ([(0:UInt8)⋯=255; 2].toArray.get! 127) == (254 : UInt8)
#assert ([(0:UInt8)⋯=254; 2].toArray.get! 127) == (254 : UInt8)
#assert ([(0:UInt8)⋯=255; -2].toArray.get! 127) == (0 : UInt8)
#assert ([(0:UInt8)⋯=254; -2].toArray.get! 127) == (0 : UInt8)

