import Cube.Kph1
open Std
def arrLine (a : Array Nat) : String := " ".intercalate (a.toList.map toString)
#eval show IO Unit from do
  IO.FS.writeFile "/root/inter/eoL.txt" ("\n".intercalate (eoL.map arrLine))
  IO.FS.writeFile "/root/inter/coL.txt" ("\n".intercalate (coL.map arrLine))
  IO.FS.writeFile "/root/inter/mL.txt" ("\n".intercalate (mL.map arrLine))
  IO.FS.writeFile "/root/inter/eIdx0.txt" (toString [eIdx[eoL[0]!]!, cIdx[coL[0]!]!, sIdx[mL[0]!]!, i0])
  IO.FS.writeFile "/root/inter/TE.txt" (arrLine TE)
  IO.FS.writeFile "/root/inter/TC.txt" (arrLine TC)
  IO.FS.writeFile "/root/inter/TS.txt" (arrLine TS)
  IO.FS.writeBinFile "/root/inter/k1dist.bin" (distF ())
  IO.println "k1 done"
