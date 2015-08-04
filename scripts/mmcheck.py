#!/usr/bin/env python3

"""mmcheck.py - a Python metamath proof verifier.

-Scott Fenton <sctfen@gmail.com>"""

import sys
import os.path
import itertools

class MMError(Exception): pass
class MMKeyError(MMError, KeyError): pass
class MMVerifyError(MMError): pass

def read_raw(fh):
    """Read in a metamath file and return tokens one-by-one."""

    for line in fh:
        for tok in line.split():
            yield tok
    return

def read_nocomment(fh):
    """Read in a metamath file and skip comments."""

    in_comment = False
    for tok in read_raw(fh):
        if tok == '$(': in_comment = True
        if not in_comment: yield tok
        if tok == '$)': in_comment = False
    return

def read(fname):
    """Read in a metamath file and return tokens, skipping comments
    and processing file include commands"""

    opened_files = {os.path.realpath(fname)}
    file_stack = [read_nocomment(open(fname,'r'))]

    while file_stack:
        did_include = False
        f = file_stack[-1]
        for tok in f:
            if f == '$[':
                fname = next(f)
                if next(f) != '$]':
                    raise MMError('File inclusion command not terminated')
                fname = os.path.realpath(fname)
                if fname not in opened_files:
                    did_include = True
                    file_stack.append(read_nocomment(open(fname, 'r')))
                    break
            else:
                yield tok
        if not did_include:
            file_stack.pop()
    return

def read_to_period(gen):
    """Read tokens from a generator until a $. token. Returns a tuple
    of the read tokens"""

    res = []
    for tok in gen:
        if tok == '$.':
            break
        else:
            res.append(tok)
    return tuple(res)

class FrameStack(list):
    """Represent a stack of frames in a Metamath file. Holds constants,
    variables, disjoint variable requirements, and hypotheses."""

    def push(self):
        self.append({'consts': set(), 'vars' : set(),
                     'essential_hyps' : [], 'floating_hyps' : [],
                     'disjoint_vars' : set()})

    def _lookup_cvd(self, typ, tok):
        """Helper for lookup_c, lookup_v, and lookup_d"""

        return any((tok in f['consts'] for f in self))

    def lookup_c(self, tok):
        """Check if tok is declared as a constant in the current context"""

        return self._lookup_cvd('consts', tok)

    def lookup_v(self, tok):
        """Check if tok is declared as a variable in the current context"""

        return self._lookup_cvd('vars', tok)

    def lookup_d(self, v1, v2):
        """Check if v1 and v2 have a disjoint variable requirement in
        the current context"""

        return self._lookup_cvd('disjoint_vars', (min(v1,v2), max(v1,v2)))

    def _add_cvd(self, typ, tok):
        """Helper for add_c, add_v, and add_d"""

        self[-1][typ].add(tok)

    def add_c(self, tok):
        """Add tok to the current constants"""

        self._add_cvd('consts', tok)

    def add_v(self, tok):
        """Add tok to the current variables"""

        self._add_cvd('vars', tok)

    def add_d(self, v1, v2):
        """Add a disjoint variable requirement to v1 and v2"""

        self._add_cvd('disjoint_vars', (min(v1,v2), max(v1,v2)))

    def _lookup_ef(self, typ, lbl):
        """Helper for lookup_e and lookup_f"""

        for f in self:
            for l, s in f[typ]:
                if lbl == l:
                    return s
        raise MMKeyError((typ,lbl))

    def lookup_e(self, lbl):
        """Get the essential hypothesis corresponding to the label
        lbl"""

        return self._lookup_ef('essential_hyps', lbl)

    def lookup_f(self, lbl):
        """Get the floating hypothesis corresponding to the label
        lbl"""

        return self._lookup_ef('essential_hyps', lbl)

    def _add_ef(self, typ, lbl, stmt):
        """Helper for add_e and add_f"""

        self[-1][typ].append((lbl, stmt))

    def add_e(self, lbl, stmt):
        """Add an essential hypothesis with label lbl and statement stmt"""

        self._add_ef('essential_hyps', lbl, stmt)

    def add_f(self, lbl, stmt):
        """Add a floating hypothesis with label lbl and statement stmt"""

        self._add_ef('floating_hyps', lbl, stmt)

    def varsof(self, stmt):
        """Get the variables in stmt given the current context"""

        return {t for t in stmt if self.lookup_v(t)}

    def get_context(self, stmt):
        """Get the disjoint variable requirements, floating hypothesis
        labels, and essential hypothesis labels needed for the given
        statement in the current context"""

        varsof = self.varsof(stmt)
        dvs = {(min(v1,v2),max(v1,v2))
               for v1, v2 in itertools.product(varsof, varsof)
               if self.lookup_d(v1, v2)}
        e_hyps = [e[0] for f in self for e in f['essential_hyps']]
        f_hyps = []
        for f_lbl, f_stmt in itertools.chain(*[f['floating_hyps']
                                               for f in self]):
            if f_stmt[1] in varsof:
                f_hyps.append(f_lbl)
        return (dvs, f_hyps, e_hyps, stmt)

class MMVerify:
    """Go through a given iterator of Metamath tokens and verify the
    proofs"""

    def __init__(self):
        self.labels = {}
        self.stack = FrameStack()

    def read(self, toks):
        """Read in a stream of Metamath tokens and verify all the proofs"""

        stack = self.stack
        labels = self.labels
        label = None

        stack.push()
        for tok in toks:
            if tok == '${':
                stack.push()
            elif tok == '$}':
                stack.pop()
            elif tok == '$c':
                for t in read_to_period(toks): stack.add_c(t)
            elif tok == '$v':
                for t in read_to_period(toks): stack.add_v(t)
            elif tok == '$f':
                stmt = read_to_period(toks)
                if not label: raise MMError('$f must have label')
                if len(stmt) != 2: raise MMError('$f must have length 2')
                stack.add_f(label, stmt)
                labels[label] = ('$f', stmt)
            elif tok == '$a':
                if not label: raise MMError('$a must have label')
                labels[label] = ('$a',
                                 stack.get_context(read_to_period(toks)))
                label = None
            elif tok == '$e':
                if not label: raise MMError('$e must have label')
                stmt = read_to_period(toks)
                stack.add_e(label, stmt)
                labels[label] = ('$e', stmt)
                label = None
            elif tok == '$p':
                if not label: raise MMError('$p must have label')
                stmt = read_to_period(toks)
                proof = None
                try:
                    i = stmt.index('$=')
                    proof = stmt[i+1:]
                    stmt = stmt[:i]
                    print(label)
                except ValueError:
                    raise MMError('$p must contain proof after $=')
                try:
                    self.verify(label, stmt, proof)
                except MMVerifyError as e:
                    print('warning:', label, 'is unproven:', e)
                self.labels[label] = ('$p', stack.get_context(stmt))
                label = None
            elif tok == '$d':
                dvs = read_to_period(toks)
                for x, y in itertools.product(dvs, repeat=2):
                    if x != y: stack.add_d(x,y)
            elif tok[0] != '$':
                label = tok
            else:
                print('tok:', tok)

    def verify(self, label, stmt, proof):
        """Verify that proof is a valid proof of stmt"""

        stack = []
        fs = self.stack
        labels = self.labels
        dvs, f_hyps, e_hyps, stmt = self.stack.get_context(stmt)

        for label in self.get_proof_steps(proof, f_hyps, e_hyps):
            steptyp, stepdat = labels[label]

            if steptyp in ('$a', '$p'):
                step_dvs, step_f, step_e, res = stepdat
                npop = len(step_f) + len(step_e)
                sp = len(stack) - npop
                if sp < 0: raise MMVerifyError('stack underflow')
                try:
                    subs = {}
                    for l, (k, v) in map(labels.get, step_f):
                        entry = stack[sp]
                        if entry[0] != k:
                            raise MMVerifyError(("stack entry ({0}, {1}) " +
                                                 "doesn't " +
                                                 "match $f hyp {2!s}")
                                                .format(k, v, entry))
                        subs[v] = entry[1:]
                        sp += 1
                    for x, y in step_dvs:
                        x_vars = fs.varsof(subs[x])
                        y_vars = fs.varsof(subs[y])
                        for x, y in itertools.product(x_vars, y_vars):
                            if x == y or not fs.lookup_d(x, y):
                                raise MMVerifyError("DV violation: {0}, {1}"
                                                    .format(x,y))
                    for l, h in map(labels.get, step_e):
                        entry = stack[sp]
                        subs_h = self.apply_subs(h, subs)
                        if entry != subs_h:
                            raise MMVerifyError(
                                "stack entry {0!s} doesn't match hyp {1!s}"
                                .format(entry, subs_h))
                        sp += 1
                    del stack[len(stack) - npop:]
                except IndexError:
                    raise MMVerifyError("stack underflow")
                stack.append(self.apply_subs(res, subs))
            elif steptyp in ('$e', '$f'):
                stack.append(stepdat)
        if len(stack) != 1:
            raise MMVerifyError('stack has >1 entry at end')
        if stack[0] != stmt:
            raise MMVerifyError('assertion proved does not match')

    def apply_subs(self, stmt, subs):
        """Apply the specified substitutions to stmt"""

        res = []
        for tok in stmt:
            res.extend(subs.get(tok, [tok]))
        return tuple(res)

    def get_proof_steps(self, proof, f_hyps, e_hyps):
        """Get the steps in the given proof."""

        for step in proof:
            if step == '?':
                raise MMVerifyError("Unproven step")
            else:
                yield step
        return

if __name__ == '__main__':
    mm = MMVerify()
    mm.read(read(sys.argv[1]))
