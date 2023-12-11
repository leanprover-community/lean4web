import Lean
import Lake.Load.Manifest

/-! # Print packages

This file contains a helper tool for the webeditor, `#package_version`, which
prints the current lean version together with a list of packages and their current
commit hashes.

-/

open Lean

namespace String

/-- Allows us to write `⟨s, 0, 7⟩` for a `Substring` instead of `⟨s, ⟨0⟩, ⟨7⟩⟩`. -/
instance : OfNat String.Pos x := ⟨⟨x⟩⟩

/-- A slice of a string. The index `start` is included `stop` excluded.
Note that this copies the string. Use `Substring` to get a slice without copying. -/
def slice (s : String) (start := 0) (stop := s.length) : String := Substring.toString ⟨s, ⟨start⟩, ⟨stop⟩⟩

end String

/-- Read the `lake-manifest.jsoin` -/
def getPackageVersions : IO String := do

  -- Get the Lean version
  let out := [s!"Lean: v{Lean.versionString}"]

  match (← Lake.Manifest.load? ⟨"lake-manifest.json"⟩) with
  | none =>
    let out := out.append ["(could not read lake-manifest.json!)"]
    return "\n\n".intercalate out
  | some manifest =>
    let out := out.append <| Array.toList <| manifest.packages.map (fun p =>
      match p with
      | .path name _ _ _ _ =>
        s!"{name}:\nlocal package"
      | .git name _ _ _ url rev _ _ =>
        let rev := rev.slice 0 7
        s!"{name}:\n{rev}\n{url}/commits/{rev}")
    return "\n\n".intercalate out

/-- Print the lean version and all available packages. -/
elab "#package_version" : command => do
  match getPackageVersions.run' () with
| none => panic ""
| some s =>
  logInfo s
