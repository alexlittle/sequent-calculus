class SequentCalculus:
    symbol_map = {
        '|': '\lor ',
        '&': '\land ',
        '-': '\\neg ',
        '>': '\\to '
    }

    proof_lines = []
    top_level_rewrite_line = None

    def convert(self, e):
        if isinstance(e, str):
            return e.upper()
        elif isinstance(e, tuple):
            if len(e) == 2 and e[0] == '-':
                return f"{self.symbol_map['-']}{self.convert(e[1])}"
            elif len(e) == 3:
                return f"({self.convert(e[0])} {self.symbol_map.get(e[1], e[1])} {self.convert(e[2])})"
        return ''

    def to_katex(self, expression):
        return ', '.join(self.convert(e) for e in expression)

    def get_indent(self, level):
        return ('  ' * level) + '- '

    def format_line(self, level, left, right, rule):
        line = f"{self.get_indent(level)}[Level {level}]$\;\; {self.to_katex(left)} \implies {self.to_katex(right)} _{{[{rule}]}}$"
        return line

    def format_axiom_line(self, level, left, right):
        line = f"{self.get_indent(level)}[Level {level}]$\;\; {self.to_katex(left)} \implies {self.to_katex(right)}$ - AXIOM"
        return line

    def format_nonaxiom_line(self, level, left, right):
        line = f"{self.get_indent(level)}[Level {level}]$\;\; {self.to_katex(left)} \implies {self.to_katex(right)}$ - NON-ATOMIC AXIOM"
        return line

    # Simplified rewrite_implications as it no longer needs to store lines, just return the result
    def rewrite_implications(self, expr):
        if isinstance(expr, str):
            return expr
        elif isinstance(expr, tuple):
            if len(expr) == 3 and expr[1] == '>':
                # Base case for implication rewrite: A > B -> -A | B
                new_left = self.rewrite_implications(expr[0])
                new_right = self.rewrite_implications(expr[2])
                return (('-', new_left), '|', new_right)
            elif len(expr) == 3:
                # Recurse into binary connectives other than '>'
                a = self.rewrite_implications(expr[0])
                b = self.rewrite_implications(expr[2])
                return (a, expr[1], b)
            elif len(expr) == 2 and expr[0] == '-':
                # Recurse into negation
                inner = self.rewrite_implications(expr[1])
                return ('-', inner)
        return expr

    def prove(self, left, right, level=0):

        # re-init if starting new proof
        if level == 0:
            self.proof_lines = []
            self.top_level_rewrite_line = None

            # Check if any rewriting is needed
            rewritten_left = set(self.rewrite_implications(f) for f in left)
            rewritten_right = set(self.rewrite_implications(f) for f in right)

            # Check if the set of formulas changed after rewriting
            if left != rewritten_left or right != rewritten_right:
                # Add the original sequent as the *conclusion* of the rewrite step
                self.top_level_rewrite_line = self.format_line(level, left, right, '\\to r.w.')

                # Update the formulas for the next level (the premise of the rewrite)
                left = rewritten_left
                right = rewritten_right
                level += 1  # Start the main proof search at the next level

        # --- Sequent Calculus Rules (now starting from the (potentially) rewritten sequent) ---

        if left & right:
            line = self.format_axiom_line(level, left, right)
            self.proof_lines.append(line)
            return (True, left, right, "AXIOM")

        for f in left:
            if isinstance(f, tuple) and f[0] == '-':
                sub_proof = self.prove(left - {f}, right | {f[1]}, level + 1)
                line = self.format_line(level, left, right, '\\neg \implies')
                self.proof_lines.append(line)
                return (sub_proof[0], left, right, "-L", f, sub_proof)

        # ... (rest of the Sequent Calculus rules remain the same) ...
        # NOTE: I'm only including the first rule for brevity, assume all rules below are unchanged.

        for f in right:
            if isinstance(f, tuple) and f[0] == '-':
                sub_proof = self.prove(left | {f[1]}, right - {f}, level + 1)
                line = self.format_line(level, left, right, '\implies \\neg')
                self.proof_lines.append(line)
                return (sub_proof[0], left, right, "-R", f, sub_proof)

        for f in left:
            if isinstance(f, tuple) and f[1] == '&':
                sub_proof = self.prove((left - {f}) | {f[0], f[2]}, right, level + 1)
                line = self.format_line(level, left, right, '\land \implies')
                self.proof_lines.append(line)
                return (sub_proof[0], left, right, "&L", f, sub_proof)

        for f in right:
            if isinstance(f, tuple) and f[1] == '&':
                sub_proof_1 = self.prove(left, (right - {f}) | {f[0]}, level + 1)
                sub_proof_2 = self.prove(left, (right - {f}) | {f[2]}, level + 1)
                line = self.format_line(level, left, right, '\implies \land')
                self.proof_lines.append(line)
                return (sub_proof_1[0] and sub_proof_2[0], left, right, "&R", f, [sub_proof_1, sub_proof_2])

        for f in right:
            if isinstance(f, tuple) and f[1] == '|':
                sub_proof = self.prove(left, (right - {f}) | {f[0], f[2]}, level + 1)
                line = self.format_line(level, left, right, '\implies \lor')
                self.proof_lines.append(line)
                return (sub_proof[0], left, right, "|R", f, sub_proof)

        for f in left:
            if isinstance(f, tuple) and f[1] == '|':
                sub_proof_1 = self.prove((left - {f}) | {f[0]}, right, level + 1)
                sub_proof_2 = self.prove((left - {f}) | {f[2]}, right, level + 1)
                line = self.format_line(level, left, right, '\lor \implies')
                self.proof_lines.append(line)
                return (sub_proof_1[0] and sub_proof_2[0], left, right, "|L", f, [sub_proof_1, sub_proof_2])

        line = self.format_nonaxiom_line(level, left, right)
        self.proof_lines.append(line)
        return (False, left, right, "Atomic non-axiom!")

    def write_to_file(self, filename):
        reversed_proof = list(reversed(self.proof_lines))

        output_lines = []

        # If a top-level rewrite occurred, prepend it to the output list.
        # This ensures it is the first line (Level 0 conclusion).
        if self.top_level_rewrite_line:
            output_lines.append(self.top_level_rewrite_line)
            # The proof steps that follow are the premises of the rewrite.
            output_lines.extend(reversed_proof)
        else:
            # If no rewrite, the reversed_proof starts with the Level 0 sequent.
            output_lines.extend(reversed_proof)

        with open(filename, 'w') as f:
            for line in output_lines:
                f.write(line + '\n')

sq = SequentCalculus()
sq.prove({(('p','|','q'),'|','r'),(('-','p'),'|','s'),('-',('q','&',('-','s')))},{('r','|','s')})
sq.write_to_file('proof3.md')

print(sq.prove({('-',('p','&',('-','q')))},{('p','>',('q','|','p'))}))
sq.write_to_file('proof2.md')