const lean4webConfig = {
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
    { "folder": "lean4web-tools",
      "name": "Stable Lean" },
    { "folder": "DuperDemo",
      "name": "Duper",
      "examples": [
        { "file": "DuperDemo.lean",
          "name": "Duper" }]
    }
  ],
  "serverCountry": "Germany",
  "contactInformation": <>
      <a href="https://www.math.hhu.de/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/jon-eugster">Jon Eugster</a><br />
      Mathematisches Institut der Heinrich-Heine-Universität Düsseldorf<br />
      Universitätsstr. 1<br />
      40225 Düsseldorf<br />
      Germany<br />
      +49 211 81-12173<br />
    </>

}

export default lean4webConfig
