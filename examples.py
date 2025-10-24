from sequent_calculus_prover import SequentCalculus

sq = SequentCalculus()

sq.prove({('-',('p','&',('-','q')))},{('p','>','q',)})
sq.write_to_file('example-proof.md')