from sequent_calculus_prover import SequentCalculus

sq = SequentCalculus()

# sq.prove({('-',('p','&',('-','q')))},{('p','>','q',)})
# sq.write_to_file('example-proof-new.md')

# sq.prove({('-', ('p', '&', 'q'))}, {(('-', 'p'), "|",  ('-', 'q'))} )
# sq.write_to_file('de_morgans.md')
#Out[1]: {('-', ('𝑝', '&', '𝑞'))} {('-', ('𝑝', '|', ('-', '𝑞')))}
md=sq.prove_from_string('¬(𝑝∧𝑞)⇒(¬𝑝∨¬𝑞)',False)
pass
# md=markdown_sq=sq.prove_from_string('((P∨Q)∨R),(¬P ∨S),¬(Q∧¬S)⇒(R∨S)')
# sq.write_to_file('example-proof-from-string.md')