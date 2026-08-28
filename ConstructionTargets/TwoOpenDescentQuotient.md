# TwoOpenDescentQuotient

This target chooses a subordinate two-open subdivision for each path and uses
the compiled homotopy invariance theorem to descend its evaluation to
`Path.Homotopic.Quotient`.

`quotientEvaluation_mk` removes the choice from the public interface: on every
path representative, the descended morphism equals `D.evaluate S` for any
supplied subordinate subdivision `S`. Certificate independence comes from
`evaluate_eq_of_subdivisions`; representative independence comes from
`evaluate_eq_of_homotopic`.

This packet does not yet package a functor. The next exact obligations are the
identity formula for a reflexive-path subdivision and the composition formula
for a subdivision of `Path.trans`, followed by the corresponding quotient
identity and composition laws.
