import { LeanWebConfig } from './docs' // look here for documentation of the individual config options

const lean4webConfig : LeanWebConfig = {
  "projects": [
    { "folder": "MathlibDemo",
      "name": "Latest Mathlib",
      "examples": [
        { "file": "MathlibDemo/Bijection.lean",
          "name": "Bijection" },
        { "file": "MathlibDemo/Logic.lean",
          "name": "Logic" },
        { "file": "MathlibDemo/Ring.lean",
          "name": "Ring" },
        { "file": "MathlibDemo/Rational.lean",
          "name": "Rational" }]},
    { "folder": "mathlib-stable",
      "name": "Mathlib stable"},
    { "folder": "mathlib-v4.24.0",
      "name": "Mathlib v4.24.0"},
    { "folder": "mathlib-v4.20.0-rc5",
      "name": "Mathlib v4.20.0-rc5"},
    { "folder": "lean-nightly",
      "name": "Lean Nightly (without mathlib)"}
  ],
  "serverCountry": 'Finland',
  "contactDetails": null,
  "impressum": null
}

export default lean4webConfig
