import LeanMirror.Examples.Classical

def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (IO.userError "usage: lake env lean --run scripts/ExportClassical.lean OUTPUT.tex")
  IO.FS.writeFile destination LeanMirror.Examples.Classical.latexDocument
