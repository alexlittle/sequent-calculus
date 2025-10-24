# Sequent Calculus Prover

Updated version of Dr Brandon Bennett's Sequent Calculus Prover.

## Basic updates...

- Includes rewriting sequents of the form $P\to Q$ to be $\neg P \lor Q$
- Creates an output file, markdown and [KaTeX](https://katex.org/) format, in a hierarchical (list) structure

## Example Usage

```
from sequent_calculus_prover import SequentCalculus
sq = SequentCalculus()
sq.prove({('-',('p','&',('-','q')))},{('p','>','q')})
sq.write_to_file('example-proof.md')
```

The [created file]('example-proof.md') can be viewed in many markdown readers showing the full logical symbols.