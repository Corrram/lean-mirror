import LeanMirror.Examples.AnalysisPresentation

def main (args : List String) : IO Unit := do
  match args with
  | [output] => IO.FS.writeFile output LeanMirror.Examples.Analysis.analysisDocument.pretty
  | _ => throw (IO.userError "Usage: lake env lean --run scripts/ExportAnalysis.lean OUTPUT.json")
