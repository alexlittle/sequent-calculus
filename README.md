# Sequent Calculus Prover

Updated version of Dr Brandon Bennett's Sequent Calculus Prover base on his [Google Collab](https://colab.research.google.com/drive/1AtY3qY32nCcGYyaUeMkdYvZNGxrmj4bt#scrollTo=-qwIlSga7zvz)

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

The [created file](example-proof.md) can be viewed in many markdown readers showing the full logical symbols.

## Improvements needed

- would be great to have a better way to visualise the "split" sequents, when an expression gets divided in two so 
    they're on the same level