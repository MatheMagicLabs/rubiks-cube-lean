import CubeH.Kph2
open Std
def arrLine (a : Array Nat) : String := " ".intercalate (a.toList.map toString)
#eval show IO Unit from do
  IO.FS.writeFile "/root/inter/cpGL.txt" ("\n".intercalate (cpGL.toList.map arrLine))
  IO.FS.writeFile "/root/inter/epGL.txt" ("\n".intercalate (epGL.toList.map arrLine))
  IO.FS.writeFile "/root/inter/clsT.txt" (arrLine clsT)
  IO.FS.writeFile "/root/inter/syT.txt" (arrLine syT)
  IO.FS.writeFile "/root/inter/repsT.txt" (arrLine repsT)
  IO.FS.writeFile "/root/inter/stabT.txt" ("\n".intercalate (stabT.toList.map (fun l => arrLine l.toArray)))
  IO.FS.writeFile "/root/inter/epCj.txt" (arrLine epCj)
  IO.FS.writeFile "/root/inter/idCell.txt" (toString idCell)
  IO.FS.writeBinFile "/root/inter/k2dist.bin" (dist2F ())
  IO.println "k2 done"
