import { Project } from './docs' // look here for documentation of the individual config options

const lean4webConfig : {
  projects: Project[],
  serverCountry: string | null
  contactDetails: JSX.Element | null
  impressum: JSX.Element | null
} = {
  "projects": [
    { "folder": "mathlib-demo",
      "name": "Latest Mathlib",
      "examples": [
        { "file": "MathlibLatest/Bijection.lean",
          "name": "Bijection" },
        { "file": "MathlibLatest/Logic.lean",
          "name": "Logic" },
        { "file": "MathlibLatest/Ring.lean",
          "name": "Ring" },
        { "file": "MathlibLatest/Rational.lean",
          "name": "Rational" }]},
    { "folder": "stable",
      "name": "Stable Lean" },
    { "folder": "DuperDemo",
      "name": "Duper",
      "examples": [
        { "file": "DuperDemo.lean",
          "name": "Duper" }]},
  ],
  "serverCountry": null,
  // example:
  // <>
  //   <p>my name</p>
  //   <p>my email</p>
  // </>,
  "contactDetails": null,
  // example:
  // <>
  //   <p>our VAT number is ...</p>
  // </>
  "impressum": null
}

export default lean4webConfig
